import os
import shutil
import threading
import time
import imaplib
import smtplib
import email as email_lib
import mimetypes
import uuid
import hmac
import hashlib
import secrets
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders as email_encoders
from datetime import datetime, date, timedelta
from functools import wraps
from flask import Flask, render_template, request, redirect, url_for, session, flash, send_file, send_from_directory, jsonify, make_response, abort
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from database import get_db, init_db, next_customer_number

app = Flask(__name__)
_secret = os.environ.get("SECRET_KEY", "")
if not _secret or _secret == "dev-secret-key":
    import sys
    print("WARNING: SECRET_KEY not set or using default — set a random value in docker-compose.yml", file=sys.stderr)
    _secret = secrets.token_hex(32)
app.secret_key = _secret

# Session security
app.config.update(
    SESSION_COOKIE_HTTPONLY  = True,
    SESSION_COOKIE_SAMESITE  = "Lax",
    SESSION_COOKIE_SECURE    = False,   # set True when serving over HTTPS
    PERMANENT_SESSION_LIFETIME = 8 * 3600,  # 8 hours
    MAX_CONTENT_LENGTH       = 20 * 1024 * 1024,  # 20 MB upload limit
)

# Password encryption for DB-stored secrets (SMTP/IMAP)
def _fernet():
    """Derive a Fernet-compatible key from SECRET_KEY."""
    import base64
    raw = hashlib.sha256(app.secret_key.encode()).digest()
    return base64.urlsafe_b64encode(raw)

def encrypt_secret(plaintext: str) -> str:
    if not plaintext:
        return ""
    key = _fernet()
    # Simple XOR-based encryption using HMAC key stream (no extra deps)
    import base64
    k = hashlib.sha256(key).digest()
    data = plaintext.encode()
    encrypted = bytes(b ^ k[i % len(k)] for i, b in enumerate(data))
    return "enc:" + base64.urlsafe_b64encode(encrypted).decode()

def decrypt_secret(ciphertext: str) -> str:
    if not ciphertext or not ciphertext.startswith("enc:"):
        return ciphertext or ""
    import base64
    key = _fernet()
    k = hashlib.sha256(key).digest()
    encrypted = base64.urlsafe_b64decode(ciphertext[4:])
    return bytes(b ^ k[i % len(k)] for i, b in enumerate(encrypted)).decode()

# ── CSRF ──────────────────────────────────────────────────────────────────────

def _csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_hex(24)
    return session["_csrf"]

def _csrf_valid():
    token = request.form.get("_csrf_token") or request.headers.get("X-CSRF-Token", "")
    expected = session.get("_csrf", "")
    return expected and hmac.compare_digest(token, expected)

app.jinja_env.globals["csrf_token"] = _csrf_token

def csrf_protect(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if request.method in ("POST", "PUT", "DELETE", "PATCH"):
            if not _csrf_valid():
                abort(403)
        return f(*args, **kwargs)
    return decorated

# ── Login Rate-Limiting ────────────────────────────────────────────────────────

_login_attempts = {}  # ip -> [timestamp, ...]
_LOGIN_MAX   = 10
_LOGIN_WINDOW = 300   # 5 minutes

def _check_rate_limit(ip):
    now = time.time()
    attempts = [t for t in _login_attempts.get(ip, []) if now - t < _LOGIN_WINDOW]
    _login_attempts[ip] = attempts
    return len(attempts) >= _LOGIN_MAX

def _record_attempt(ip):
    _login_attempts.setdefault(ip, []).append(time.time())

def _clear_attempts(ip):
    _login_attempts.pop(ip, None)


UPLOAD_DIR  = os.path.join(os.path.dirname(__file__), "data", "uploads")
DOC_STORE   = os.path.join(os.path.dirname(__file__), "data", "documents")


def get_feed_data():
    db = get_db()
    messages = db.execute(
        "SELECT id, user_id, username, body, attachment, created_at FROM feed_messages ORDER BY created_at ASC LIMIT 100"
    ).fetchall()
    ticket_count = db.execute("SELECT COUNT(*) FROM tickets WHERE is_read=0").fetchone()[0]
    invoice_count = db.execute("SELECT COUNT(*) FROM invoices WHERE status='sent'").fetchone()[0]
    db.close()
    return [dict(m) for m in messages], ticket_count, invoice_count


@app.context_processor
def inject_globals():
    db = get_db()
    app_cfg = get_settings(db)
    db.close()
    is_kg = (app_cfg.get("company_kleingewerbe") == "1")
    def brutto(amount):
        if is_kg:
            return float(amount)
        return round(float(amount) * 1.19, 2)
    if 'user_id' not in session:
        return {'app_cfg': app_cfg, 'is_kg': is_kg, 'brutto': brutto}
    messages, ticket_count, invoice_count = get_feed_data()
    db2 = get_db()
    urow = db2.execute("SELECT avatar FROM users WHERE id=?", (session["user_id"],)).fetchone()
    payout_count = db2.execute(
        "SELECT COUNT(*) FROM promoter_payouts WHERE status='pending'"
    ).fetchone()[0]
    db2.close()
    current_user_avatar = urow["avatar"] if urow and urow["avatar"] else None
    return {'feed_messages': messages, 'ticket_count': ticket_count,
            'invoice_count': invoice_count, 'app_cfg': app_cfg,
            'current_user_avatar': current_user_avatar,
            'payout_count': payout_count, 'is_kg': is_kg, 'brutto': brutto}


def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if "user_id" not in session:
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated


# CSRF check for all state-changing requests from logged-in users
_CSRF_EXEMPT = {"login", "promoter_register", "static"}

@app.before_request
def enforce_csrf_and_session():
    # Session timeout: log out after 8h of inactivity
    if "user_id" in session:
        last_active = session.get("_last_active", time.time())
        if time.time() - last_active > 8 * 3600:
            session.clear()
            flash("Sitzung abgelaufen. Bitte erneut anmelden.", "error")
            return redirect(url_for("login"))
        session["_last_active"] = time.time()

    # CSRF
    if request.method not in ("POST", "PUT", "DELETE", "PATCH"):
        return
    endpoint = request.endpoint or ""
    if endpoint in _CSRF_EXEMPT:
        return
    if "user_id" not in session:
        return
    if not _csrf_valid():
        abort(403)


def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if "user_id" not in session:
            return redirect(url_for("login"))
        if session.get("role", "admin") != "admin":
            flash("Kein Zugriff – nur für Admins.", "error")
            return redirect(url_for("promoter_dashboard"))
        return f(*args, **kwargs)
    return decorated


def _calc_commission_for_invoice(db, invoice_id):
    """Check if this invoice triggers a promoter commission. Creates entry if yes."""
    inv = db.execute("SELECT * FROM invoices WHERE id=?", (invoice_id,)).fetchone()
    if not inv or not inv["customer_id"]:
        return
    inv_date = inv["date"]
    assignments = db.execute("""
        SELECT * FROM promoter_assignments
        WHERE customer_id=?
          AND start_date <= ?
          AND (end_date IS NULL OR end_date >= ?)
    """, (inv["customer_id"], inv_date, inv_date)).fetchall()
    for a in assignments:
        # avoid duplicate commission for same invoice+assignment
        exists = db.execute(
            "SELECT id FROM promoter_commissions WHERE assignment_id=? AND invoice_id=?",
            (a["id"], invoice_id)).fetchone()
        if exists:
            continue
        total = db.execute(
            "SELECT COALESCE(SUM(quantity*unit_price),0) as t FROM invoice_items WHERE invoice_id=?",
            (invoice_id,)).fetchone()["t"]
        commission = round(total * a["commission_pct"] / 100, 2)
        db.execute("""
            INSERT INTO promoter_commissions (assignment_id, invoice_id, invoice_total, commission_pct, amount)
            VALUES (?,?,?,?,?)
        """, (a["id"], invoice_id, total, a["commission_pct"], commission))


def next_invoice_number():
    db = get_db()
    row = db.execute("SELECT number FROM invoices ORDER BY id DESC LIMIT 1").fetchone()
    db.close()
    if not row:
        return f"RE-{date.today().year}-001"
    last = row["number"]
    try:
        num = int(last.split("-")[-1]) + 1
        return f"RE-{date.today().year}-{num:03d}"
    except Exception:
        return f"RE-{date.today().year}-001"


# ── Feed messages ─────────────────────────────────────────────────────────────

@app.route("/feed/send", methods=["POST"])
@login_required
def feed_send():
    body = request.form.get("body", "").strip()
    attachment = None
    f = request.files.get("file")
    if f and f.filename:
        os.makedirs(UPLOAD_DIR, exist_ok=True)
        safe = f"{datetime.now().strftime('%Y%m%d_%H%M%S')}_{secure_filename(f.filename)}"
        f.save(os.path.join(UPLOAD_DIR, safe))
        attachment = safe
    if body or attachment:
        db = get_db()
        db.execute("INSERT INTO feed_messages (user_id, username, body, attachment) VALUES (?,?,?,?)",
                   (session["user_id"], session["username"], body or "", attachment))
        db.commit()
        db.close()
    return redirect(request.referrer or url_for("dashboard"))


@app.route("/feed/message/<int:mid>/edit", methods=["POST"])
@login_required
def feed_message_edit(mid):
    body = request.form.get("body", "").strip()
    if body:
        db = get_db()
        msg = db.execute("SELECT user_id FROM feed_messages WHERE id=?", (mid,)).fetchone()
        if msg and msg["user_id"] == session["user_id"]:
            db.execute("UPDATE feed_messages SET body=? WHERE id=?", (body, mid))
            db.commit()
        db.close()
    return redirect(request.referrer or url_for("dashboard"))


@app.route("/feed/message/<int:mid>/delete", methods=["POST"])
@login_required
def feed_message_delete(mid):
    db = get_db()
    msg = db.execute("SELECT user_id FROM feed_messages WHERE id=?", (mid,)).fetchone()
    if msg and msg["user_id"] == session["user_id"]:
        db.execute("DELETE FROM feed_messages WHERE id=?", (mid,))
        db.commit()
    db.close()
    return redirect(request.referrer or url_for("dashboard"))


@app.route("/uploads/<path:filename>")
@login_required
def uploaded_file(filename):
    # Prevent path traversal: only allow plain filenames, no subdirectories
    safe = os.path.basename(filename)
    if not safe or safe != filename:
        abort(400)
    return send_from_directory(UPLOAD_DIR, safe, as_attachment=True)


@app.route("/feed/messages")
@login_required
def feed_messages_json():
    db = get_db()
    rows = db.execute("""
        SELECT fm.id, fm.user_id, fm.username, fm.body, fm.attachment, fm.created_at,
               u.avatar, u.display_name
        FROM feed_messages fm
        LEFT JOIN users u ON fm.user_id = u.id
        ORDER BY fm.created_at ASC LIMIT 100
    """).fetchall()
    db.close()
    return jsonify([dict(r) for r in rows])


# ── Auth ──────────────────────────────────────────────────────────────────────

@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        ip = request.remote_addr or "unknown"
        if _check_rate_limit(ip):
            flash("Zu viele Anmeldeversuche. Bitte 5 Minuten warten.", "error")
            return render_template("login.html")
        db = get_db()
        user = db.execute("SELECT * FROM users WHERE username=?", (request.form.get("username", ""),)).fetchone()
        db.close()
        if user and check_password_hash(user["password_hash"], request.form.get("password", "")):
            _clear_attempts(ip)
            session["user_id"] = user["id"]
            session["username"] = user["username"]
            session["display_name"] = user["display_name"] or user["username"]
            session["role"] = user["role"] or "admin"
            dest = url_for("promoter_dashboard") if session["role"] == "promoter" else url_for("dashboard")
            resp = make_response(redirect(dest))
            resp.set_cookie("last_uid",          str(user["id"]),                          max_age=30*24*3600)
            resp.set_cookie("last_display_name", user["display_name"] or user["username"], max_age=30*24*3600)
            return resp
        _record_attempt(ip)
        flash("Falscher Benutzername oder Passwort", "error")
    return render_template("login.html")


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


# ── Dashboard ─────────────────────────────────────────────────────────────────

@app.route("/")
@login_required
def dashboard():
    db = get_db()
    stats = {
        "customers":       db.execute("SELECT COUNT(*) FROM customers WHERE status='customer'").fetchone()[0],
        "leads":           db.execute("SELECT COUNT(*) FROM customers WHERE status='lead'").fetchone()[0],
        "tickets_open":    db.execute("SELECT COUNT(*) FROM tickets WHERE status='open'").fetchone()[0],
        "tickets_progress":db.execute("SELECT COUNT(*) FROM tickets WHERE status='in_progress'").fetchone()[0],
        "invoices_unpaid": db.execute("SELECT COUNT(*) FROM invoices WHERE status='sent'").fetchone()[0],
        "invoices_draft":  db.execute("SELECT COUNT(*) FROM invoices WHERE status='draft'").fetchone()[0],
        "revenue_month":   db.execute("""
            SELECT COALESCE(SUM(ii.quantity * ii.unit_price),0)
            FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
            WHERE i.status IN ('sent','paid') AND strftime('%Y-%m', i.date) = strftime('%Y-%m', 'now')
        """).fetchone()[0],
        "revenue_total":   db.execute("""
            SELECT COALESCE(SUM(ii.quantity * ii.unit_price),0)
            FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
            WHERE i.status IN ('sent','paid')
        """).fetchone()[0],
    }
    recent_tickets = db.execute("""
        SELECT t.*, c.name as customer_name FROM tickets t
        LEFT JOIN customers c ON t.customer_id = c.id
        WHERE t.status != 'closed'
        ORDER BY CASE t.priority WHEN 'high' THEN 1 WHEN 'medium' THEN 2 ELSE 3 END, t.created_at DESC
        LIMIT 6
    """).fetchall()
    recent_invoices = db.execute("""
        SELECT i.*, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total
        FROM invoices i LEFT JOIN customers c ON i.customer_id = c.id
        ORDER BY i.created_at DESC LIMIT 5
    """).fetchall()
    from datetime import datetime
    db.close()
    return render_template("dashboard.html", stats=stats,
                           recent_tickets=recent_tickets, recent_invoices=recent_invoices,
                           now_hour=datetime.now().hour)


# ── Kunden ────────────────────────────────────────────────────────────────────

@app.route("/customers")
@login_required
def customers():
    db = get_db()
    q = request.args.get("q", "")
    status = request.args.get("status", "")
    query = "SELECT * FROM customers WHERE 1=1"
    params = []
    if q:
        query += " AND (name LIKE ? OR company LIKE ? OR email LIKE ?)"
        params += [f"%{q}%", f"%{q}%", f"%{q}%"]
    if status:
        query += " AND status=?"
        params.append(status)
    query += " ORDER BY created_at DESC"
    rows = db.execute(query, params).fetchall()
    db.close()
    return render_template("customers.html", customers=rows, q=q, status=status)


def _customer_fields(form):
    return (
        form.get("customer_number"), form.get("company"), form.get("legal_form"),
        form.get("name"), form.get("email"), form.get("phone"), form.get("website"),
        form.get("street"), form.get("zip"), form.get("city"), form.get("country"),
        form.get("tax_id"), form.get("payment_terms"),
        form.get("contact_person"), form.get("contact_position"),
        form.get("contact_email"), form.get("contact_phone"), form.get("contact_mobile"),
        form.get("contract_type"), form.get("support_level"),
        form.get("contract_start") or None, form.get("contract_end") or None,
        float(form["monthly_rate"]) if form.get("monthly_rate") else None,
        int(form["num_workstations"]) if form.get("num_workstations") else None,
        int(form["num_servers"]) if form.get("num_servers") else None,
        form.get("it_notes"), form.get("source"), form.get("notes"), form.get("status"),
    )


@app.route("/customers/new", methods=["GET", "POST"])
@login_required
def customer_new():
    db = get_db()
    if request.method == "POST":
        fields = _customer_fields(request.form)
        db.execute("""INSERT INTO customers
            (customer_number,company,legal_form,name,email,phone,website,
             street,zip,city,country,tax_id,payment_terms,
             contact_person,contact_position,contact_email,contact_phone,contact_mobile,
             contract_type,support_level,contract_start,contract_end,monthly_rate,
             num_workstations,num_servers,it_notes,source,notes,status)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""", fields)
        db.commit()
        db.close()
        flash("Kunde angelegt", "success")
        return redirect(url_for("customers"))
    kd_nr = next_customer_number(db)
    db.close()
    return render_template("customer_form.html", customer=None, kd_nr=kd_nr)


@app.route("/customers/<int:cid>/edit", methods=["GET", "POST"])
@login_required
def customer_edit(cid):
    db = get_db()
    customer = db.execute("SELECT * FROM customers WHERE id=?", (cid,)).fetchone()
    if request.method == "POST":
        fields = _customer_fields(request.form)
        db.execute("""UPDATE customers SET
            customer_number=?,company=?,legal_form=?,name=?,email=?,phone=?,website=?,
            street=?,zip=?,city=?,country=?,tax_id=?,payment_terms=?,
            contact_person=?,contact_position=?,contact_email=?,contact_phone=?,contact_mobile=?,
            contract_type=?,support_level=?,contract_start=?,contract_end=?,monthly_rate=?,
            num_workstations=?,num_servers=?,it_notes=?,source=?,notes=?,status=?
            WHERE id=?""", (*fields, cid))
        db.commit()
        db.close()
        flash("Kunde gespeichert", "success")
        return redirect(url_for("customers"))
    db.close()
    return render_template("customer_form.html", customer=customer, kd_nr=None)


@app.route("/customers/<int:cid>/delete", methods=["POST"])
@login_required
def customer_delete(cid):
    db = get_db()
    # invoice_items cascade automatically when invoice is deleted
    inv_ids = [r[0] for r in db.execute(
        "SELECT id FROM invoices WHERE customer_id=?", (cid,)).fetchall()]
    for iid in inv_ids:
        db.execute("DELETE FROM invoice_items WHERE invoice_id=?", (iid,))
    if inv_ids:
        db.execute(f"DELETE FROM invoices WHERE id IN ({','.join('?'*len(inv_ids))})", inv_ids)
    db.execute("UPDATE tickets  SET customer_id=NULL WHERE customer_id=?", (cid,))
    db.execute("DELETE FROM outreach WHERE customer_id=?", (cid,))
    db.execute("DELETE FROM customers WHERE id=?", (cid,))
    db.commit()
    db.close()
    flash("Kunde gelöscht", "success")
    return redirect(url_for("customers"))


# ── Rechnungen ────────────────────────────────────────────────────────────────

@app.route("/invoices")
@login_required
def invoices():
    db = get_db()
    rows = db.execute("""
        SELECT i.*, c.name as customer_name, c.company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total
        FROM invoices i JOIN customers c ON i.customer_id=c.id
        ORDER BY i.created_at DESC
    """).fetchall()
    db.close()
    return render_template("invoices.html", invoices=rows)


@app.route("/invoices/new", methods=["GET", "POST"])
@login_required
def invoice_new():
    db = get_db()
    if request.method == "POST":
        number = next_invoice_number()
        db.execute("""INSERT INTO invoices (number, customer_id, date, due_date, status, notes)
                      VALUES (?,?,?,?,?,?)""",
                   (number, request.form["customer_id"], request.form["date"],
                    request.form["due_date"], request.form["status"], request.form["notes"]))
        inv_id = db.execute("SELECT last_insert_rowid()").fetchone()[0]
        descs = request.form.getlist("desc[]")
        qtys = request.form.getlist("qty[]")
        prices = request.form.getlist("price[]")
        for desc, qty, price in zip(descs, qtys, prices):
            if desc.strip():
                db.execute("INSERT INTO invoice_items (invoice_id, description, quantity, unit_price) VALUES (?,?,?,?)",
                           (inv_id, desc, float(qty), float(price)))
        db.commit()
        db.close()
        flash(f"Rechnung {number} erstellt", "success")
        return redirect(url_for("invoices"))
    customers = db.execute("SELECT * FROM customers ORDER BY name").fetchall()
    articles  = db.execute("SELECT * FROM articles WHERE active=1 ORDER BY category, name").fetchall()
    cfg = get_settings(db)
    db.close()
    return render_template("invoice_form.html", invoice=None, customers=customers,
                           articles=articles, cfg=cfg,
                           today=date.today().isoformat(), number=next_invoice_number())


@app.route("/invoices/<int:iid>")
@login_required
def invoice_view(iid):
    db = get_db()
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.company, c.street, c.zip, c.city,
                                   c.country, c.email, c.tax_id as customer_tax_id
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=?""", (iid,)).fetchone()
    items = db.execute("SELECT * FROM invoice_items WHERE invoice_id=?", (iid,)).fetchall()
    total = sum(it["quantity"] * it["unit_price"] for it in items)
    email_log = db.execute("SELECT * FROM invoice_emails WHERE invoice_id=? ORDER BY sent_at DESC", (iid,)).fetchall()
    cfg = get_settings(db)
    db.close()
    return render_template("invoice_view.html", invoice=invoice, items=items, total=total,
                           email_log=email_log, cfg=cfg)


def generate_invoice_pdf_bytes(iid, db):
    from io import BytesIO
    from xhtml2pdf import pisa
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.company as customer_company,
                                   c.street, c.zip, c.city, c.email, c.tax_id as customer_tax_id
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=?""", (iid,)).fetchone()
    items   = db.execute("SELECT * FROM invoice_items WHERE invoice_id=?", (iid,)).fetchall()
    total   = sum(it["quantity"] * it["unit_price"] for it in items)
    cfg     = get_settings(db)
    data_dir = os.path.join(os.path.dirname(__file__), "data")
    html_str = render_template("invoice_pdf.html", invoice=invoice, items=items, total=total, cfg=cfg,
                               doc_store=data_dir)
    buf = BytesIO()
    pisa.CreatePDF(html_str.encode("utf-8"), dest=buf)
    return buf.getvalue()


@app.route("/invoices/<int:iid>/pdf")
@login_required
def invoice_pdf(iid):
    db = get_db()
    invoice = db.execute("SELECT number FROM invoices WHERE id=?", (iid,)).fetchone()
    try:
        pdf = generate_invoice_pdf_bytes(iid, db)
    finally:
        db.close()
    from flask import Response
    return Response(pdf, mimetype="application/pdf",
                    headers={"Content-Disposition": f'attachment; filename="Rechnung_{invoice["number"]}.pdf"'})


@app.route("/invoices/<int:iid>/send-email", methods=["POST"])
@login_required
def invoice_send_email(iid):
    db = get_db()
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.email as customer_email
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=?""", (iid,)).fetchone()
    to_addr = request.form.get("to_email", "").strip() or (invoice["customer_email"] if invoice else "")
    subject = request.form.get("subject", f"Rechnung {invoice['number']}").strip()
    body    = request.form.get("body", "").strip()
    if not to_addr:
        flash("Keine E-Mail-Adresse angegeben", "error")
        db.close()
        return redirect(url_for("invoice_view", iid=iid))
    try:
        cfg = get_settings(db)
        # Generate PDF
        pdf_bytes = generate_invoice_pdf_bytes(iid, db)
        # Build message
        host       = cfg.get("smtp_host", "").strip()
        port       = int(cfg.get("smtp_port", 587) or 587)
        user       = cfg.get("smtp_user", "").strip()
        pw         = cfg.get("smtp_pass", "")
        from_name  = cfg.get("smtp_from_name", "tkToolkit").strip() or "tkToolkit"
        from_email = (cfg.get("smtp_from_email", "") or user).strip()
        if not host:
            raise ValueError("SMTP nicht konfiguriert (Host fehlt)")
        msg = MIMEMultipart()
        msg["From"]    = f"{from_name} <{from_email}>"
        msg["To"]      = to_addr
        msg["Subject"] = subject
        msg.attach(MIMEText(body, "plain", "utf-8"))
        # Attach PDF
        pdf_part = MIMEBase("application", "pdf")
        pdf_part.set_payload(pdf_bytes)
        email_encoders.encode_base64(pdf_part)
        pdf_part.add_header("Content-Disposition", f'attachment; filename="Rechnung_{invoice["number"]}.pdf"')
        msg.attach(pdf_part)
        # Send
        if port == 465:
            with smtplib.SMTP_SSL(host, port, timeout=20) as s:
                s.login(user, pw)
                s.sendmail(from_email, to_addr, msg.as_string())
        else:
            with smtplib.SMTP(host, port, timeout=20) as s:
                s.ehlo(); s.starttls(); s.ehlo()
                s.login(user, pw)
                s.sendmail(from_email, to_addr, msg.as_string())
        db.execute("INSERT INTO invoice_emails (invoice_id, to_addr, subject, sent_by) VALUES (?,?,?,?)",
                   (iid, to_addr, subject, session["username"]))
        if invoice["status"] == "draft":
            db.execute("UPDATE invoices SET status='sent' WHERE id=?", (iid,))
        _calc_commission_for_invoice(db, iid)
        db.commit()
        flash(f"Rechnung als PDF an {to_addr} gesendet ✓", "success")
    except Exception as e:
        flash(f"E-Mail-Fehler: {e}", "error")
    db.close()
    return redirect(url_for("invoice_view", iid=iid))


@app.route("/invoices/<int:iid>/status/<status>", methods=["POST"])
@login_required
def invoice_status(iid, status):
    db = get_db()
    db.execute("UPDATE invoices SET status=? WHERE id=?", (status, iid))
    if status in ("sent", "paid"):
        _calc_commission_for_invoice(db, iid)
    db.commit()
    db.close()
    return redirect(url_for("invoice_view", iid=iid))


@app.route("/invoices/<int:iid>/delete", methods=["POST"])
@login_required
def invoice_delete(iid):
    db = get_db()
    db.execute("DELETE FROM invoices WHERE id=?", (iid,))
    db.commit()
    db.close()
    flash("Rechnung gelöscht", "success")
    return redirect(url_for("invoices"))


# ── Settings helpers ──────────────────────────────────────────────────────────

_SECRET_KEYS = {"smtp_pass", "imap_pass"}

def get_settings(db=None):
    close = db is None
    if db is None:
        db = get_db()
    rows = db.execute("SELECT key, value FROM settings").fetchall()
    result = {}
    for r in rows:
        v = r["value"]
        if r["key"] in _SECRET_KEYS:
            v = decrypt_secret(v)
        result[r["key"]] = v
    if close:
        db.close()
    return result


def save_setting(key, value, db=None):
    close = db is None
    if db is None:
        db = get_db()
    if key in _SECRET_KEYS and value:
        value = encrypt_secret(value)
    db.execute("INSERT INTO settings (key,value) VALUES (?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
               (key, value))
    if close:
        db.commit()
        db.close()


def send_smtp_email(to_addr, subject, body_text, settings=None):
    if settings is None:
        settings = get_settings()
    host = settings.get("smtp_host", "").strip()
    port = int(settings.get("smtp_port", 587) or 587)
    user = settings.get("smtp_user", "").strip()
    pw   = settings.get("smtp_pass", "")
    from_name  = settings.get("smtp_from_name", "tkToolkit").strip() or "tkToolkit"
    from_email = (settings.get("smtp_from_email", "") or user).strip()
    if not host:
        raise ValueError("SMTP nicht konfiguriert (Host fehlt)")
    if not user:
        raise ValueError("SMTP-Benutzername fehlt")
    msg = MIMEMultipart("alternative")
    msg["From"]    = f"{from_name} <{from_email}>"
    msg["To"]      = to_addr
    msg["Subject"] = subject
    msg.attach(MIMEText(body_text, "plain", "utf-8"))
    try:
        if port == 465:
            with smtplib.SMTP_SSL(host, port, timeout=20) as s:
                s.login(user, pw)
                s.sendmail(from_email, to_addr, msg.as_string())
        else:
            with smtplib.SMTP(host, port, timeout=20) as s:
                s.ehlo()
                s.starttls()
                s.ehlo()
                s.login(user, pw)
                s.sendmail(from_email, to_addr, msg.as_string())
    except smtplib.SMTPAuthenticationError:
        raise ValueError("SMTP-Authentifizierung fehlgeschlagen – Benutzername/Passwort prüfen")
    except smtplib.SMTPConnectError as e:
        raise ValueError(f"Verbindung zu {host}:{port} fehlgeschlagen – {e}")
    except OSError as e:
        raise ValueError(f"Netzwerkfehler – Hostname '{host}' nicht erreichbar: {e}")


# ── Tickets ───────────────────────────────────────────────────────────────────

@app.route("/tickets")
@login_required
def tickets():
    db = get_db()
    status = request.args.get("status", "")
    query = """SELECT t.*, c.name as customer_name FROM tickets t
               LEFT JOIN customers c ON t.customer_id=c.id WHERE 1=1"""
    params = []
    if status:
        query += " AND t.status=?"
        params.append(status)
    query += " ORDER BY t.created_at DESC"
    rows = db.execute(query, params).fetchall()
    db.close()
    return render_template("tickets.html", tickets=rows, status=status)


@app.route("/tickets/new", methods=["GET", "POST"])
@login_required
def ticket_new():
    db = get_db()
    if request.method == "POST":
        db.execute("""INSERT INTO tickets (title, description, customer_id, priority, status)
                      VALUES (?,?,?,?,?)""",
                   (request.form["title"], request.form["description"],
                    request.form["customer_id"] or None,
                    request.form["priority"], request.form["status"]))
        db.commit()
        db.close()
        flash("Ticket erstellt", "success")
        return redirect(url_for("tickets"))
    customers = db.execute("SELECT * FROM customers ORDER BY name").fetchall()
    db.close()
    return render_template("ticket_form.html", ticket=None, customers=customers)


@app.route("/tickets/<int:tid>/edit", methods=["GET", "POST"])
@login_required
def ticket_edit(tid):
    db = get_db()
    ticket = db.execute("SELECT * FROM tickets WHERE id=?", (tid,)).fetchone()
    if request.method == "POST":
        db.execute("""UPDATE tickets SET title=?, description=?, customer_id=?, priority=?, status=?,
                      updated_at=CURRENT_TIMESTAMP WHERE id=?""",
                   (request.form["title"], request.form["description"],
                    request.form["customer_id"] or None,
                    request.form["priority"], request.form["status"], tid))
        db.commit()
        db.close()
        flash("Ticket gespeichert", "success")
        return redirect(url_for("tickets"))
    customers = db.execute("SELECT * FROM customers ORDER BY name").fetchall()
    db.close()
    return render_template("ticket_form.html", ticket=ticket, customers=customers)


@app.route("/tickets/<int:tid>/delete", methods=["POST"])
@login_required
def ticket_delete(tid):
    db = get_db()
    db.execute("DELETE FROM tickets WHERE id=?", (tid,))
    db.commit()
    db.close()
    flash("Ticket gelöscht", "success")
    return redirect(url_for("tickets"))


@app.route("/tickets/<int:tid>")
@login_required
def ticket_detail(tid):
    db = get_db()
    ticket = db.execute("""
        SELECT t.*, c.name as customer_name, c.email as customer_email,
               c.company as customer_company
        FROM tickets t LEFT JOIN customers c ON t.customer_id=c.id
        WHERE t.id=?""", (tid,)).fetchone()
    if not ticket:
        db.close()
        flash("Ticket nicht gefunden", "error")
        return redirect(url_for("tickets"))
    updates = db.execute(
        "SELECT * FROM ticket_updates WHERE ticket_id=? ORDER BY created_at ASC", (tid,)
    ).fetchall()
    customers = db.execute("SELECT id, name, company, email FROM customers ORDER BY name").fetchall()
    db.execute("UPDATE tickets SET is_read=1 WHERE id=?", (tid,))
    db.commit()
    db.close()
    return render_template("ticket_detail.html", ticket=ticket, updates=updates, customers=customers)


@app.route("/tickets/<int:tid>/update", methods=["POST"])
@login_required
def ticket_update_post(tid):
    db = get_db()
    body       = request.form.get("body", "").strip()
    new_status = request.form.get("status")
    update_type = request.form.get("update_type", "comment")
    hours   = int(request.form.get("time_h", 0) or 0)
    minutes = int(request.form.get("time_m", 0) or 0)
    time_minutes = hours * 60 + minutes

    if new_status:
        old = db.execute("SELECT * FROM tickets WHERE id=?", (tid,)).fetchone()
        if old and old["status"] != new_status:
            labels = {"open": "Offen", "in_progress": "In Arbeit", "closed": "Gelöst"}
            status_note = f"Status geändert: {labels.get(old['status'], old['status'])} → {labels.get(new_status, new_status)}"
            db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                          VALUES (?,?,?,?,?)""",
                       (tid, session["user_id"], session["username"], status_note, "status_change"))

            # auto-email customer when ticket is closed
            if new_status == "closed" and old:
                cust = db.execute(
                    "SELECT c.email, c.name FROM customers c WHERE c.id=?",
                    (old["customer_id"],)).fetchone() if old["customer_id"] else None
                if cust and cust["email"]:
                    try:
                        settings = get_settings(db)
                        title = old["title"]
                        company = settings.get("company_name", "")
                        close_body = (
                            f"Hallo {cust['name']},\n\n"
                            f"Ihr Ticket #{tid} '{title}' wurde soeben als geloest markiert.\n\n"
                            f"Falls Sie weitere Fragen haben, antworten Sie einfach auf diese E-Mail.\n\n"
                            f"Mit freundlichen Gruessen\n{company}"
                        )
                        send_smtp_email(
                            cust["email"],
                            f"[#{tid}] Ihr Ticket wurde geschlossen",
                            close_body,
                            settings)
                        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                                      VALUES (?,?,?,?,?)""",
                                   (tid, session["user_id"], session["username"],
                                    f"Automatische Abschluss-Mail an {cust['email']} gesendet.", "email_sent"))
                    except Exception as e:
                        print(f"[TICKET] Abschluss-Mail Fehler: {e}")

        db.execute("UPDATE tickets SET status=?, updated_at=CURRENT_TIMESTAMP WHERE id=?", (new_status, tid))

    if body:
        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type, time_minutes)
                      VALUES (?,?,?,?,?,?)""",
                   (tid, session["user_id"], session["username"], body, update_type, time_minutes))
        db.execute("UPDATE tickets SET is_read=0, updated_at=CURRENT_TIMESTAMP WHERE id=?", (tid,))

    db.commit()
    db.close()
    if new_status == "closed":
        return redirect(url_for("tickets"))
    return redirect(url_for("ticket_detail", tid=tid))


@app.route("/tickets/<int:tid>/send-email", methods=["POST"])
@login_required
def ticket_send_email(tid):
    db = get_db()
    ticket = db.execute("""SELECT t.*, c.email as customer_email, c.name as customer_name
                            FROM tickets t LEFT JOIN customers c ON t.customer_id=c.id
                            WHERE t.id=?""", (tid,)).fetchone()
    to_addr  = request.form.get("to_email", "").strip() or (ticket["customer_email"] if ticket else "")
    default_subject = f"[#{tid}] {ticket['title'] if ticket else ''}"
    subject  = request.form.get("subject", default_subject).strip()
    # ensure ticket reference is always in subject for reply matching
    if f"[#{tid}]" not in subject:
        subject = f"[#{tid}] {subject}"
    body_txt = request.form.get("body", "").strip()

    if not to_addr:
        flash("Keine E-Mail-Adresse angegeben", "error")
        db.close()
        return redirect(url_for("ticket_detail", tid=tid))

    try:
        settings = get_settings(db)
        send_smtp_email(to_addr, subject, body_txt, settings)
        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                      VALUES (?,?,?,?,?)""",
                   (tid, session["user_id"], session["username"],
                    f"E-Mail gesendet an {to_addr}\n\nBetreff: {subject}\n\n{body_txt}", "email_sent"))
        db.commit()
        flash(f"E-Mail an {to_addr} gesendet", "success")
    except Exception as e:
        flash(f"E-Mail-Fehler: {e}", "error")
    db.close()
    return redirect(url_for("ticket_detail", tid=tid))


# ── Akquise ───────────────────────────────────────────────────────────────────

@app.route("/outreach")
@login_required
def outreach():
    db = get_db()
    leads = db.execute("SELECT * FROM customers WHERE status='lead' ORDER BY name").fetchall()
    history = db.execute("""SELECT o.*, c.name as customer_name FROM outreach o
                            JOIN customers c ON o.customer_id=c.id
                            ORDER BY o.sent_at DESC LIMIT 50""").fetchall()
    db.close()
    return render_template("outreach.html", leads=leads, history=history)


@app.route("/outreach/send", methods=["POST"])
@login_required
def outreach_send():
    db = get_db()
    cids = request.form.getlist("customer_ids")
    subject = request.form["subject"]
    body = request.form["body"]
    for cid in cids:
        db.execute("INSERT INTO outreach (customer_id, subject, body) VALUES (?,?,?)", (cid, subject, body))
    db.commit()
    db.close()
    flash(f"{len(cids)} Anschreiben gespeichert", "success")
    return redirect(url_for("outreach"))


# ── Leistungen / Artikelkatalog ───────────────────────────────────────────────

@app.route("/articles")
@login_required
def articles():
    db = get_db()
    rows = db.execute("SELECT * FROM articles ORDER BY category, name").fetchall()
    db.close()
    return render_template("articles.html", articles=rows)


@app.route("/articles/search")
@login_required
def articles_search():
    q = request.args.get("q", "")
    db = get_db()
    rows = db.execute(
        "SELECT * FROM articles WHERE (name LIKE ? OR description LIKE ?) AND active=1 LIMIT 8",
        (f"%{q}%", f"%{q}%")
    ).fetchall()
    db.close()
    return jsonify([dict(r) for r in rows])


def _next_article_number(conn):
    row = conn.execute("SELECT article_number FROM articles WHERE article_number IS NOT NULL ORDER BY id DESC LIMIT 1").fetchone()
    if not row or not row["article_number"]:
        return "ART-0001"
    try:
        return f"ART-{int(row['article_number'].split('-')[1])+1:04d}"
    except Exception:
        return "ART-0001"


@app.route("/articles/new", methods=["GET", "POST"])
@login_required
def article_new():
    db = get_db()
    if request.method == "POST":
        db.execute("""INSERT INTO articles (article_number,name,description,category,unit,unit_price,tax_rate,active)
                      VALUES (?,?,?,?,?,?,?,?)""",
                   (request.form["article_number"], request.form["name"], request.form["description"],
                    request.form["category"], request.form["unit"],
                    float(request.form["unit_price"] or 0),
                    float(request.form["tax_rate"] or 19),
                    1 if request.form.get("active") else 0))
        db.commit()
        db.close()
        flash("Leistung angelegt", "success")
        return redirect(url_for("articles"))
    nr = _next_article_number(db)
    db.close()
    return render_template("article_form.html", article=None, art_nr=nr)


@app.route("/articles/<int:aid>/edit", methods=["GET", "POST"])
@login_required
def article_edit(aid):
    db = get_db()
    article = db.execute("SELECT * FROM articles WHERE id=?", (aid,)).fetchone()
    if request.method == "POST":
        db.execute("""UPDATE articles SET article_number=?,name=?,description=?,category=?,unit=?,
                      unit_price=?,tax_rate=?,active=? WHERE id=?""",
                   (request.form["article_number"], request.form["name"], request.form["description"],
                    request.form["category"], request.form["unit"],
                    float(request.form["unit_price"] or 0),
                    float(request.form["tax_rate"] or 19),
                    1 if request.form.get("active") else 0, aid))
        db.commit()
        db.close()
        flash("Leistung gespeichert", "success")
        return redirect(url_for("articles"))
    db.close()
    return render_template("article_form.html", article=article, art_nr=None)


@app.route("/articles/<int:aid>/delete", methods=["POST"])
@login_required
def article_delete(aid):
    db = get_db()
    db.execute("DELETE FROM articles WHERE id=?", (aid,))
    db.commit()
    db.close()
    flash("Leistung gelöscht", "success")
    return redirect(url_for("articles"))


# ── Dokumente ─────────────────────────────────────────────────────────────────

def _doc_breadcrumb(db, folder_id):
    crumbs = []
    fid = folder_id
    while fid:
        row = db.execute("SELECT id, name, parent_id FROM documents WHERE id=? AND type='folder'", (fid,)).fetchone()
        if not row:
            break
        crumbs.insert(0, dict(row))
        fid = row["parent_id"]
    return crumbs


@app.route("/documents")
@app.route("/documents/<int:folder_id>")
@login_required
def documents(folder_id=None):
    db = get_db()
    if folder_id:
        folder = db.execute("SELECT * FROM documents WHERE id=? AND type='folder'", (folder_id,)).fetchone()
        if not folder:
            db.close()
            return redirect(url_for("documents"))
    else:
        folder = None
    items = db.execute(
        "SELECT * FROM documents WHERE parent_id IS ? ORDER BY type DESC, name ASC",
        (folder_id,)
    ).fetchall()
    crumbs = _doc_breadcrumb(db, folder_id) if folder_id else []
    db.close()
    return render_template("documents.html", items=items, folder=folder, folder_id=folder_id, crumbs=crumbs)


@app.route("/documents/new-folder", methods=["POST"])
@login_required
def document_new_folder():
    name      = request.form.get("name", "").strip()
    parent_id = request.form.get("parent_id") or None
    if name:
        db = get_db()
        db.execute("INSERT INTO documents (name, parent_id, type, uploaded_by) VALUES (?,?,?,?)",
                   (name, parent_id, "folder", session["username"]))
        db.commit()
        db.close()
    if parent_id:
        return redirect(url_for("documents", folder_id=parent_id))
    return redirect(url_for("documents"))


@app.route("/documents/upload", methods=["POST"])
@login_required
def document_upload():
    parent_id = request.form.get("parent_id") or None
    os.makedirs(DOC_STORE, exist_ok=True)
    for f in request.files.getlist("files"):
        if not f.filename:
            continue
        ext     = os.path.splitext(f.filename)[1]
        safe    = f"{uuid.uuid4().hex}{ext}"
        f.save(os.path.join(DOC_STORE, safe))
        size    = os.path.getsize(os.path.join(DOC_STORE, safe))
        mime, _ = mimetypes.guess_type(f.filename)
        db = get_db()
        db.execute("""INSERT INTO documents (name, parent_id, type, file_path, file_size, mime_type, uploaded_by)
                      VALUES (?,?,?,?,?,?,?)""",
                   (f.filename, parent_id, "file", safe, size, mime or "application/octet-stream", session["username"]))
        db.commit()
        db.close()
    flash("Datei(en) hochgeladen", "success")
    if parent_id:
        return redirect(url_for("documents", folder_id=parent_id))
    return redirect(url_for("documents"))


@app.route("/documents/<int:did>/download")
@login_required
def document_download(did):
    db = get_db()
    doc = db.execute("SELECT * FROM documents WHERE id=? AND type='file'", (did,)).fetchone()
    db.close()
    if not doc:
        flash("Datei nicht gefunden", "error")
        return redirect(url_for("documents"))
    safe_fp = os.path.basename(doc["file_path"])
    if not safe_fp:
        abort(400)
    return send_from_directory(DOC_STORE, safe_fp, as_attachment=True,
                               download_name=secure_filename(doc["name"] or safe_fp))


@app.route("/documents/<int:did>/rename", methods=["POST"])
@login_required
def document_rename(did):
    new_name  = request.form.get("name", "").strip()
    parent_id = request.form.get("parent_id") or None
    if new_name:
        db = get_db()
        db.execute("UPDATE documents SET name=? WHERE id=?", (new_name, did))
        db.commit()
        db.close()
    if parent_id:
        return redirect(url_for("documents", folder_id=parent_id))
    return redirect(url_for("documents"))


@app.route("/documents/<int:did>/delete", methods=["POST"])
@login_required
def document_delete(did):
    parent_id = request.form.get("parent_id") or None
    db = get_db()
    doc = db.execute("SELECT * FROM documents WHERE id=?", (did,)).fetchone()
    if doc and doc["type"] == "file" and doc["file_path"]:
        fp = os.path.join(DOC_STORE, doc["file_path"])
        if os.path.exists(fp):
            os.remove(fp)
    db.execute("DELETE FROM documents WHERE id=?", (did,))
    db.commit()
    db.close()
    flash("Gelöscht", "success")
    if parent_id:
        return redirect(url_for("documents", folder_id=parent_id))
    return redirect(url_for("documents"))


@app.route("/api/counts")
@login_required
def api_counts():
    db = get_db()
    tickets  = db.execute("SELECT COUNT(*) FROM tickets WHERE status='open'").fetchone()[0]
    invoices = db.execute("SELECT COUNT(*) FROM invoices WHERE status='sent'").fetchone()[0]
    db.close()
    return jsonify(tickets=tickets, invoices=invoices)


# ── Backup ────────────────────────────────────────────────────────────────────

@app.route("/backup")
@login_required
def backup():
    data_dir = os.path.join(os.path.dirname(__file__), "data")
    src = os.path.join(data_dir, "itool.db")
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    dst = os.path.join(data_dir, f"backup_{ts}.db")
    shutil.copy2(src, dst)
    # Clean up old backups — keep only the 3 most recent
    backups = sorted(
        [f for f in os.listdir(data_dir) if f.startswith("backup_") and f.endswith(".db")],
        reverse=True
    )
    for old in backups[3:]:
        try:
            os.remove(os.path.join(data_dir, old))
        except OSError:
            pass
    return send_file(dst, as_attachment=True, download_name=f"itool_backup_{ts}.db")


# ── Settings ──────────────────────────────────────────────────────────────────

SETTING_KEYS_BY_TAB = {
    "firma": [
        "company_name", "company_street", "company_zip", "company_city",
        "company_phone", "company_email", "company_website", "company_tax_id",
        "company_iban", "company_bic", "company_bank", "company_kleingewerbe",
    ],
    "smtp": [
        "smtp_host", "smtp_port", "smtp_user", "smtp_pass",
        "smtp_from_name", "smtp_from_email",
    ],
    "imap": [
        "imap_host", "imap_port", "imap_user", "imap_pass",
        "imap_enabled", "imap_folder", "imap_auto_ticket",
    ],
}


@app.route("/settings", methods=["GET", "POST"])
@login_required
def settings():
    db = get_db()
    if request.method == "POST":
        tab  = request.form.get("_tab", "")
        keys = SETTING_KEYS_BY_TAB.get(tab, sum(SETTING_KEYS_BY_TAB.values(), []))
        for key in keys:
            val = request.form.get(key, "")
            save_setting(key, val, db)
        db.commit()
        flash("Einstellungen gespeichert", "success")
    cfg = get_settings(db)
    db.close()
    return render_template("settings.html", cfg=cfg)


def _save_logo_file(file_obj, key_prefix):
    """Save uploaded logo file, return ext or None on error."""
    if not file_obj or not file_obj.filename:
        return None
    ext = file_obj.filename.rsplit(".", 1)[-1].lower()
    if ext not in ("png", "jpg", "jpeg", "gif", "svg"):
        return "bad_ext"
    base = key_prefix  # e.g. "logo" or "invoice_logo"
    for old_ext in ("png", "jpg", "jpeg", "gif", "svg"):
        op = os.path.join(os.path.dirname(__file__), "data", f"{base}.{old_ext}")
        if os.path.exists(op):
            os.remove(op)
    file_obj.save(os.path.join(os.path.dirname(__file__), "data", f"{base}.{ext}"))
    return ext


@app.route("/settings/logo", methods=["POST"])
@login_required
def settings_logo():
    db = get_db()
    # Firmenlogo (sidebar / login)
    ext = _save_logo_file(request.files.get("logo"), "logo")
    if ext == "bad_ext":
        flash("Nur PNG, JPG, GIF oder SVG erlaubt", "error")
    elif ext:
        save_setting("company_logo_ext", ext, db)
        flash("Firmenlogo gespeichert", "success")
    # Rechnungslogo
    ext2 = _save_logo_file(request.files.get("invoice_logo"), "invoice_logo")
    if ext2 == "bad_ext":
        flash("Nur PNG, JPG, GIF oder SVG erlaubt (Rechnungslogo)", "error")
    elif ext2:
        save_setting("invoice_logo_ext", ext2, db)
        flash("Rechnungslogo gespeichert", "success")
    db.commit()
    db.close()
    return redirect(url_for("settings") + "#firma")


@app.route("/logo")
def company_logo():
    db = get_db()
    cfg = get_settings(db)
    db.close()
    ext = cfg.get("company_logo_ext", "")
    if ext:
        path = os.path.join(os.path.dirname(__file__), "data", f"logo.{ext}")
        if os.path.exists(path):
            return send_file(path)
    return ("", 404)


@app.route("/invoice-logo")
@login_required
def invoice_logo():
    db = get_db()
    cfg = get_settings(db)
    db.close()
    ext = cfg.get("invoice_logo_ext", "")
    if ext:
        path = os.path.join(os.path.dirname(__file__), "data", f"invoice_logo.{ext}")
        if os.path.exists(path):
            return send_file(path)
    # fallback to company logo
    ext2 = cfg.get("company_logo_ext", "")
    if ext2:
        path2 = os.path.join(os.path.dirname(__file__), "data", f"logo.{ext2}")
        if os.path.exists(path2):
            return send_file(path2)
    return ("", 404)


AVATAR_DIR = os.path.join(os.path.dirname(__file__), "data", "avatars")

@app.route("/avatar/<int:uid>")  # public – shown on login + chat before auth check
def user_avatar(uid):
    os.makedirs(AVATAR_DIR, exist_ok=True)
    db = get_db()
    row = db.execute("SELECT avatar FROM users WHERE id=?", (uid,)).fetchone()
    db.close()
    if row and row["avatar"]:
        path = os.path.join(AVATAR_DIR, row["avatar"])
        if os.path.exists(path):
            return send_file(path)
    return ("", 404)


@app.route("/settings/avatar", methods=["POST"])
@login_required
def settings_avatar():
    f = request.files.get("avatar")
    if f and f.filename:
        ext = f.filename.rsplit(".", 1)[-1].lower()
        if ext not in ("png", "jpg", "jpeg", "gif", "webp"):
            flash("Nur PNG, JPG, GIF oder WebP erlaubt", "error")
            return redirect(url_for("settings") + "#allgemein")
        os.makedirs(AVATAR_DIR, exist_ok=True)
        uid = session["user_id"]
        filename = f"user_{uid}.{ext}"
        # Remove old avatars for this user
        for old_ext in ("png", "jpg", "jpeg", "gif", "webp"):
            op = os.path.join(AVATAR_DIR, f"user_{uid}.{old_ext}")
            if os.path.exists(op):
                os.remove(op)
        f.save(os.path.join(AVATAR_DIR, filename))
        db = get_db()
        db.execute("UPDATE users SET avatar=? WHERE id=?", (filename, uid))
        db.commit()
        db.close()
        flash("Avatar gespeichert", "success")
    return redirect(url_for("settings") + "#allgemein")


@app.route("/settings/display-name", methods=["POST"])
@login_required
def settings_display_name():
    name = request.form.get("display_name", "").strip()
    if name:
        db = get_db()
        db.execute("UPDATE users SET display_name=? WHERE id=?", (name, session["user_id"]))
        db.commit()
        db.close()
        session["display_name"] = name
        flash("Anzeigename gespeichert", "success")
    return redirect(url_for("settings") + "#allgemein")


@app.route("/settings/change-password", methods=["POST"])
@login_required
def settings_change_password():
    current  = request.form.get("current_password", "")
    new_pw   = request.form.get("new_password", "")
    confirm  = request.form.get("confirm_password", "")
    db = get_db()
    user = db.execute("SELECT * FROM users WHERE id=?", (session["user_id"],)).fetchone()
    if not check_password_hash(user["password_hash"], current):
        flash("Aktuelles Passwort ist falsch", "error")
    elif len(new_pw) < 6:
        flash("Neues Passwort muss mindestens 6 Zeichen haben", "error")
    elif new_pw != confirm:
        flash("Passwörter stimmen nicht überein", "error")
    else:
        db.execute("UPDATE users SET password_hash=? WHERE id=?",
                   (generate_password_hash(new_pw), session["user_id"]))
        db.commit()
        flash("Passwort erfolgreich geändert", "success")
    db.close()
    return redirect(url_for("settings") + "#allgemein")


@app.route("/settings/test-smtp", methods=["POST"])
@login_required
def settings_test_smtp():
    db = get_db()
    cfg = get_settings(db)
    db.close()
    to_addr = request.form.get("test_email", "").strip()
    if not to_addr:
        flash("Bitte Test-E-Mail-Adresse eingeben", "error")
        return redirect(url_for("settings"))
    try:
        send_smtp_email(to_addr, "tkToolkit SMTP-Test", "Verbindung erfolgreich! ✓", cfg)
        flash(f"Test-E-Mail an {to_addr} gesendet ✓", "success")
    except Exception as e:
        flash(f"SMTP-Fehler: {e}", "error")
    return redirect(url_for("settings"))


# ── IMAP background polling ────────────────────────────────────────────────────

def _decode_header(value):
    parts = email_lib.header.decode_header(value or "")
    out = []
    for chunk, charset in parts:
        if isinstance(chunk, bytes):
            out.append(chunk.decode(charset or "utf-8", errors="replace"))
        else:
            out.append(chunk)
    return "".join(out)


def poll_imap_inbox():
    """Fetch UNSEEN emails and create tickets. Returns (count, error_msg)."""
    cfg = get_settings()
    if cfg.get("imap_enabled") != "1" or cfg.get("imap_auto_ticket") != "1":
        return 0, "IMAP oder Auto-Ticket nicht aktiviert"
    host   = cfg.get("imap_host", "").strip()
    port   = int(cfg.get("imap_port") or 993)
    user   = cfg.get("imap_user", "").strip()
    pw     = cfg.get("imap_pass", "")
    folder = (cfg.get("imap_folder") or "INBOX").strip()
    if not host or not user:
        return 0, "Host oder Benutzer fehlt"
    M = None
    try:
        M = imaplib.IMAP4_SSL(host, port, timeout=20)
        M.login(user, pw)
        M.select(folder)
        _, data = M.search(None, "UNSEEN")
        uids = data[0].split()
        if not uids:
            print(f"[IMAP] Keine neuen E-Mails ({host})")
            M.logout()
            return 0, None
        count = 0
        db = get_db()
        for uid in uids:
            try:
                _, msg_data = M.fetch(uid, "(RFC822)")
                raw = msg_data[0][1]
                msg = email_lib.message_from_bytes(raw)
                subject  = _decode_header(msg.get("Subject", "Kein Betreff"))[:200]
                from_hdr = _decode_header(msg.get("From", "Unbekannt"))
                # extract plain email address from "Name <addr>" format
                from_email = from_hdr
                if "<" in from_hdr and ">" in from_hdr:
                    from_email = from_hdr[from_hdr.index("<")+1:from_hdr.index(">")].strip().lower()
                else:
                    from_email = from_hdr.strip().lower()
                body = ""
                if msg.is_multipart():
                    for part in msg.walk():
                        ct = part.get_content_type()
                        if ct == "text/plain" and not part.get("Content-Disposition"):
                            body = part.get_payload(decode=True).decode(
                                part.get_content_charset("utf-8") or "utf-8", errors="replace")
                            break
                else:
                    payload = msg.get_payload(decode=True)
                    if payload:
                        body = payload.decode(msg.get_content_charset("utf-8") or "utf-8", errors="replace")
                body = (body or "").strip()[:4000]
                # match customer by email or contact_email
                cust = db.execute(
                    "SELECT id FROM customers WHERE LOWER(email)=? OR LOWER(contact_email)=? LIMIT 1",
                    (from_email, from_email)).fetchone()
                customer_id = cust["id"] if cust else None

                # check if this is a reply to an existing ticket via [#ID] in subject
                import re as _re
                tid_match = _re.search(r'\[#(\d+)\]', subject)
                if tid_match:
                    existing_tid = int(tid_match.group(1))
                    exists = db.execute("SELECT id FROM tickets WHERE id=?", (existing_tid,)).fetchone()
                    if exists:
                        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                                      VALUES (?,?,?,?,?)""",
                                   (existing_tid, None, from_hdr, body or "(kein Text)", "email_reply"))
                        db.execute("UPDATE tickets SET is_read=0, updated_at=CURRENT_TIMESTAMP WHERE id=?",
                                   (existing_tid,))
                        print(f"[IMAP] Antwort zu Ticket #{existing_tid} hinzugefügt")
                        M.store(uid, "+FLAGS", "\\Seen")
                        count += 1
                        continue

                # no match → new ticket
                db.execute(
                    "INSERT INTO tickets (title, description, priority, status, customer_id, is_read) VALUES (?,?,?,?,?,0)",
                    (subject, f"Von: {from_hdr}\n\n{body}", "medium", "open", customer_id))
                if customer_id:
                    print(f"[IMAP] Ticket Kunde zugeordnet: {from_email} → ID {customer_id}")
                M.store(uid, "+FLAGS", "\\Seen")
                count += 1
                print(f"[IMAP] Ticket erstellt: {subject}")
            except Exception as e:
                print(f"[IMAP] Fehler bei Nachricht {uid}: {e}")
        db.commit()
        db.close()
        M.logout()
        return count, None
    except Exception as e:
        print(f"[IMAP] Verbindungsfehler: {e}")
        try:
            if M:
                M.logout()
        except Exception:
            pass
        return 0, str(e)


@app.route("/settings/imap-check", methods=["POST"])
@login_required
def settings_imap_check():
    count, err = poll_imap_inbox()
    if err:
        flash(f"IMAP-Fehler: {err}", "error")
    elif count == 0:
        flash("Keine neuen E-Mails gefunden.", "success")
    else:
        flash(f"{count} neue E-Mail(s) → {count} Ticket(s) erstellt ✓", "success")
    return redirect(url_for("settings") + "#imap")


def imap_loop():
    print("[IMAP] Hintergrund-Job gestartet (Intervall: 120s)")
    while True:
        try:
            count, err = poll_imap_inbox()
            if err:
                print(f"[IMAP] Poll-Fehler: {err}")
            elif count:
                print(f"[IMAP] {count} neue(s) Ticket(s) erstellt")
        except Exception as e:
            print(f"[IMAP] Unerwarteter Fehler: {e}")
        time.sleep(120)


# ── Promoter ──────────────────────────────────────────────────────────────────

@app.route("/register/<token>", methods=["GET", "POST"])
def promoter_register(token):
    db = get_db()
    tok = db.execute(
        "SELECT * FROM promoter_tokens WHERE token=? AND used_by IS NULL", (token,)).fetchone()
    if not tok:
        db.close()
        return render_template("promoter_register.html", error="Ungültiger oder bereits verwendeter Link.")
    # Token expires after 72 hours
    created = datetime.strptime(tok["created_at"][:19], "%Y-%m-%d %H:%M:%S")
    if datetime.utcnow() - created > timedelta(hours=72):
        db.close()
        return render_template("promoter_register.html", error="Dieser Link ist abgelaufen (72h). Bitte neuen Link anfordern.")
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        display  = request.form.get("display_name", "").strip()
        pw       = request.form.get("password", "")
        pw2      = request.form.get("password2", "")
        if not username or not pw:
            return render_template("promoter_register.html", error="Benutzername und Passwort erforderlich.")
        if pw != pw2:
            return render_template("promoter_register.html", error="Passwörter stimmen nicht überein.")
        if db.execute("SELECT id FROM users WHERE username=?", (username,)).fetchone():
            return render_template("promoter_register.html", error="Benutzername bereits vergeben.")
        phash = generate_password_hash(pw)
        cur = db.execute(
            "INSERT INTO users (username, password_hash, display_name, role) VALUES (?,?,?,?)",
            (username, phash, display or username, "promoter"))
        new_uid = cur.lastrowid
        db.execute("UPDATE promoter_tokens SET used_by=?, used_at=CURRENT_TIMESTAMP WHERE id=?",
                   (new_uid, tok["id"]))
        db.commit()
        db.close()
        flash("Registrierung erfolgreich – bitte anmelden.", "success")
        return redirect(url_for("login"))
    db.close()
    return render_template("promoter_register.html", error=None)


@app.route("/promoters")
@admin_required
def promoters():
    db = get_db()
    rows = db.execute("""
        SELECT u.id, u.username, u.display_name, u.avatar,
               COUNT(DISTINCT pa.id) as assignment_count,
               COALESCE(SUM(CASE WHEN pp.status='pending' THEN pp.amount END), 0) as pending_payout,
               COALESCE(SUM(CASE WHEN pp.status='approved' THEN pp.amount END), 0) as paid_out
        FROM users u
        LEFT JOIN promoter_assignments pa ON pa.promoter_id = u.id
        LEFT JOIN promoter_payouts pp ON pp.promoter_id = u.id
        WHERE u.role = 'promoter'
        GROUP BY u.id
        ORDER BY u.display_name
    """).fetchall()
    # pending payout requests
    payouts = db.execute("""
        SELECT pp.*, u.display_name, u.username
        FROM promoter_payouts pp
        JOIN users u ON u.id = pp.promoter_id
        WHERE pp.status = 'pending'
        ORDER BY pp.requested_at DESC
    """).fetchall()
    # unused tokens
    tokens = db.execute("""
        SELECT pt.*, u.username as created_by_name
        FROM promoter_tokens pt
        LEFT JOIN users u ON u.id = pt.created_by
        WHERE pt.used_by IS NULL
        ORDER BY pt.created_at DESC
    """).fetchall()
    db.close()
    return render_template("promoters.html", promoters=rows, payouts=payouts, tokens=tokens)


@app.route("/promoters/generate-link", methods=["POST"])
@admin_required
def promoter_generate_link():
    db = get_db()
    token = uuid.uuid4().hex
    db.execute("INSERT INTO promoter_tokens (token, created_by) VALUES (?,?)",
               (token, session["user_id"]))
    db.commit()
    db.close()
    flash(f"Registrierungslink erstellt: {request.host_url}register/{token}", "success")
    return redirect(url_for("promoters"))


@app.route("/promoters/<int:pid>")
@admin_required
def promoter_detail(pid):
    db = get_db()
    promoter = db.execute("SELECT * FROM users WHERE id=? AND role='promoter'", (pid,)).fetchone()
    if not promoter:
        db.close()
        flash("Promoter nicht gefunden.", "error")
        return redirect(url_for("promoters"))
    assignments = db.execute("""
        SELECT pa.*, c.name as customer_name, c.company as customer_company
        FROM promoter_assignments pa
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=?
        ORDER BY pa.created_at DESC
    """, (pid,)).fetchall()
    commissions = db.execute("""
        SELECT pc.*, i.number as invoice_number, i.date as invoice_date,
               c.name as customer_name
        FROM promoter_commissions pc
        JOIN promoter_assignments pa ON pa.id = pc.assignment_id
        JOIN invoices i ON i.id = pc.invoice_id
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=?
        ORDER BY pc.created_at DESC
    """, (pid,)).fetchall()
    payouts = db.execute("""
        SELECT pp.*, u.username as decided_by_name
        FROM promoter_payouts pp
        LEFT JOIN users u ON u.id = pp.decided_by
        WHERE pp.promoter_id=?
        ORDER BY pp.requested_at DESC
    """, (pid,)).fetchall()
    total_earned   = sum(c["amount"] for c in commissions)
    total_paid     = sum(p["amount"] for p in payouts if p["status"] == "approved")
    total_pending  = sum(p["amount"] for p in payouts if p["status"] == "pending")
    balance        = total_earned - total_paid - total_pending
    customers_list = db.execute(
        "SELECT id, name, company FROM customers ORDER BY name").fetchall()
    db.close()
    return render_template("promoter_detail.html",
                           promoter=promoter, assignments=assignments,
                           commissions=commissions, payouts=payouts,
                           total_earned=total_earned, total_paid=total_paid,
                           total_pending=total_pending, balance=balance,
                           customers_list=customers_list)


@app.route("/promoters/<int:pid>/assign", methods=["POST"])
@admin_required
def promoter_assign(pid):
    db = get_db()
    db.execute("""
        INSERT INTO promoter_assignments (promoter_id, customer_id, commission_pct, start_date, end_date, notes, created_by)
        VALUES (?,?,?,?,?,?,?)
    """, (pid,
          request.form["customer_id"],
          float(request.form.get("commission_pct", 25)),
          request.form["start_date"],
          request.form.get("end_date") or None,
          request.form.get("notes", ""),
          session["user_id"]))
    db.commit()
    db.close()
    flash("Zuweisung gespeichert.", "success")
    return redirect(url_for("promoter_detail", pid=pid))


@app.route("/promoters/assignments/<int:aid>/delete", methods=["POST"])
@admin_required
def promoter_assignment_delete(aid):
    db = get_db()
    row = db.execute("SELECT promoter_id FROM promoter_assignments WHERE id=?", (aid,)).fetchone()
    db.execute("DELETE FROM promoter_assignments WHERE id=?", (aid,))
    db.commit()
    db.close()
    flash("Zuweisung entfernt.", "success")
    pid = row["promoter_id"] if row else 0
    return redirect(url_for("promoter_detail", pid=pid))


@app.route("/promoters/payouts/<int:poid>/decide", methods=["POST"])
@admin_required
def promoter_payout_decide(poid):
    decision = request.form.get("decision")  # approved / rejected
    notes    = request.form.get("admin_notes", "")
    db = get_db()
    payout = db.execute("SELECT * FROM promoter_payouts WHERE id=?", (poid,)).fetchone()
    if payout and decision in ("approved", "rejected"):
        db.execute("""
            UPDATE promoter_payouts
            SET status=?, decided_at=CURRENT_TIMESTAMP, decided_by=?, admin_notes=?
            WHERE id=?
        """, (decision, session["user_id"], notes, poid))
        if decision == "approved":
            # mark commissions as paid
            db.execute("""
                UPDATE promoter_commissions SET payout_id=?
                WHERE payout_id IS NULL
                  AND assignment_id IN (
                    SELECT id FROM promoter_assignments WHERE promoter_id=?
                  )
            """, (poid, payout["promoter_id"]))
        db.commit()
    db.close()
    flash(f"Auszahlung {'genehmigt' if decision=='approved' else 'abgelehnt'}.", "success")
    return redirect(url_for("promoters"))


# ── Promoter-eigenes Dashboard ─────────────────────────────────────────────────

@app.route("/promoter")
@login_required
def promoter_dashboard():
    if session.get("role") == "admin":
        return redirect(url_for("dashboard"))
    pid = session["user_id"]
    db = get_db()
    commissions = db.execute("""
        SELECT pc.*, i.number as invoice_number, i.date as invoice_date,
               c.name as customer_name, c.company as customer_company,
               pa.commission_pct
        FROM promoter_commissions pc
        JOIN promoter_assignments pa ON pa.id = pc.assignment_id
        JOIN invoices i ON i.id = pc.invoice_id
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=?
        ORDER BY pc.created_at DESC
    """, (pid,)).fetchall()
    payouts = db.execute("""
        SELECT pp.*, u.username as decided_by_name
        FROM promoter_payouts pp
        LEFT JOIN users u ON u.id = pp.decided_by
        WHERE pp.promoter_id=?
        ORDER BY pp.requested_at DESC
    """, (pid,)).fetchall()
    assignments = db.execute("""
        SELECT pa.*, c.name as customer_name, c.company as customer_company
        FROM promoter_assignments pa
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=?
    """, (pid,)).fetchall()
    total_earned  = sum(c["amount"] for c in commissions)
    total_paid    = sum(p["amount"] for p in payouts if p["status"] == "approved")
    total_pending = sum(p["amount"] for p in payouts if p["status"] == "pending")
    balance       = total_earned - total_paid - total_pending
    db.close()
    return render_template("promoter_dashboard.html",
                           commissions=commissions, payouts=payouts,
                           assignments=assignments,
                           total_earned=total_earned, total_paid=total_paid,
                           total_pending=total_pending, balance=balance)


@app.route("/promoter/request-payout", methods=["POST"])
@login_required
def promoter_request_payout():
    if session.get("role") != "promoter":
        return redirect(url_for("dashboard"))
    pid = session["user_id"]
    db = get_db()
    # balance = earned - approved - pending
    earned = db.execute("""
        SELECT COALESCE(SUM(pc.amount),0) as t FROM promoter_commissions pc
        JOIN promoter_assignments pa ON pa.id=pc.assignment_id
        WHERE pa.promoter_id=?
    """, (pid,)).fetchone()["t"]
    paid_or_pending = db.execute("""
        SELECT COALESCE(SUM(amount),0) as t FROM promoter_payouts
        WHERE promoter_id=? AND status IN ('approved','pending')
    """, (pid,)).fetchone()["t"]
    balance = round(earned - paid_or_pending, 2)
    if balance <= 0:
        flash("Kein auszahlbares Guthaben vorhanden.", "error")
        db.close()
        return redirect(url_for("promoter_dashboard"))
    db.execute("INSERT INTO promoter_payouts (promoter_id, amount) VALUES (?,?)", (pid, balance))
    db.commit()
    db.close()
    flash(f"Auszahlungsantrag über {balance:.2f} € wurde gesendet.", "success")
    return redirect(url_for("promoter_dashboard"))


# ── Zeitauswertung ────────────────────────────────────────────────────────────

@app.route("/time-report")
@login_required
def time_report():
    from datetime import datetime, timedelta
    db   = get_db()
    now  = datetime.now()
    period = request.args.get("period", "month")
    date_from = request.args.get("from", "")
    date_to   = request.args.get("to", "")

    if period == "today":
        date_from = now.strftime("%Y-%m-%d")
        date_to   = date_from
    elif period == "week":
        monday    = now - timedelta(days=now.weekday())
        date_from = monday.strftime("%Y-%m-%d")
        date_to   = now.strftime("%Y-%m-%d")
    elif period == "month":
        date_from = now.strftime("%Y-%m-01")
        date_to   = now.strftime("%Y-%m-%d")
    elif period == "year":
        date_from = now.strftime("%Y-01-01")
        date_to   = now.strftime("%Y-%m-%d")
    # else: custom → date_from/date_to from query params

    rows = db.execute("""
        SELECT tu.id, tu.ticket_id, tu.username, tu.body, tu.time_minutes, tu.created_at,
               t.title as ticket_title, c.name as customer_name, c.company as customer_company
        FROM ticket_updates tu
        JOIN tickets t ON t.id = tu.ticket_id
        LEFT JOIN customers c ON c.id = t.customer_id
        WHERE tu.time_minutes > 0
          AND DATE(tu.created_at) BETWEEN ? AND ?
        ORDER BY tu.created_at DESC
    """, (date_from, date_to)).fetchall()

    # Aggregation by customer
    by_customer = {}
    for r in rows:
        key = r["customer_company"] or r["customer_name"] or "Kein Kunde"
        by_customer[key] = by_customer.get(key, 0) + r["time_minutes"]
    by_customer = sorted(by_customer.items(), key=lambda x: -x[1])

    # Aggregation by ticket
    by_ticket = {}
    for r in rows:
        key = (r["ticket_id"], r["ticket_title"])
        by_ticket[key] = by_ticket.get(key, 0) + r["time_minutes"]
    by_ticket = sorted(by_ticket.items(), key=lambda x: -x[1])

    # Aggregation by user
    by_user = {}
    for r in rows:
        by_user[r["username"]] = by_user.get(r["username"], 0) + r["time_minutes"]
    by_user = sorted(by_user.items(), key=lambda x: -x[1])

    total_minutes = sum(r["time_minutes"] for r in rows)
    db.close()
    return render_template("time_report.html",
                           rows=rows, period=period,
                           date_from=date_from, date_to=date_to,
                           by_customer=by_customer, by_ticket=by_ticket,
                           by_user=by_user, total_minutes=total_minutes)


# ── Buchhaltung ───────────────────────────────────────────────────────────────

@app.route("/accounting")
@login_required
def accounting():
    from datetime import datetime
    db  = get_db()
    now = datetime.now()

    def revenue(where, params=()):
        return db.execute(
            f"SELECT COALESCE(SUM(ii.quantity*ii.unit_price),0) FROM invoices i "
            f"JOIN invoice_items ii ON ii.invoice_id=i.id {where}", params
        ).fetchone()[0]

    stats = {
        "revenue_month":    revenue("WHERE i.status IN ('sent','paid') AND strftime('%Y-%m',i.date)=?",
                                    (now.strftime("%Y-%m"),)),
        "revenue_year":     revenue("WHERE i.status IN ('sent','paid') AND strftime('%Y',i.date)=?",
                                    (now.strftime("%Y"),)),
        "revenue_total":    revenue("WHERE i.status IN ('sent','paid')"),
        "outstanding":      revenue("WHERE i.status='sent'"),
        "paid_month":       revenue("WHERE i.status='paid' AND strftime('%Y-%m',i.date)=?",
                                    (now.strftime("%Y-%m"),)),
        "draft_total":      revenue("WHERE i.status='draft'"),
        "count_sent":       db.execute("SELECT COUNT(*) FROM invoices WHERE status='sent'").fetchone()[0],
        "count_paid_month": db.execute("SELECT COUNT(*) FROM invoices WHERE status='paid' AND strftime('%Y-%m',date)=?",
                                       (now.strftime("%Y-%m"),)).fetchone()[0],
        "count_draft":      db.execute("SELECT COUNT(*) FROM invoices WHERE status='draft'").fetchone()[0],
    }

    # Monthly revenue for last 12 months
    monthly = db.execute("""
        SELECT strftime('%Y-%m', i.date) as month,
               SUM(ii.quantity*ii.unit_price) as total,
               COUNT(DISTINCT i.id) as count
        FROM invoices i JOIN invoice_items ii ON ii.invoice_id=i.id
        WHERE i.status IN ('sent','paid')
          AND i.date >= date('now','-12 months')
        GROUP BY month ORDER BY month
    """).fetchall()

    # Unpaid invoices (sent but not paid) — oldest first
    unpaid = db.execute("""
        SELECT i.*, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total,
               CAST(julianday('now') - julianday(i.due_date) AS INTEGER) as overdue_days
        FROM invoices i LEFT JOIN customers c ON c.id=i.customer_id
        WHERE i.status='sent'
        ORDER BY i.due_date ASC
    """).fetchall()

    # Last paid invoices
    paid_recent = db.execute("""
        SELECT i.*, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total
        FROM invoices i LEFT JOIN customers c ON c.id=i.customer_id
        WHERE i.status='paid'
        ORDER BY i.date DESC LIMIT 10
    """).fetchall()

    # Top customers by revenue
    top_customers = db.execute("""
        SELECT c.name, c.company,
               SUM(ii.quantity*ii.unit_price) as total,
               COUNT(DISTINCT i.id) as invoice_count
        FROM invoices i
        JOIN invoice_items ii ON ii.invoice_id=i.id
        JOIN customers c ON c.id=i.customer_id
        WHERE i.status IN ('sent','paid')
        GROUP BY c.id ORDER BY total DESC LIMIT 5
    """).fetchall()

    kleingewerbe = db.execute("SELECT value FROM settings WHERE key='company_kleingewerbe'").fetchone()
    is_kg = (kleingewerbe and kleingewerbe["value"] == "1")

    # Expenses
    expenses = db.execute(
        "SELECT * FROM expenses ORDER BY date DESC"
    ).fetchall()
    expenses_total = db.execute(
        "SELECT COALESCE(SUM(amount_netto * (1 + tax_rate/100.0)), 0) FROM expenses"
    ).fetchone()[0]

    db.close()
    return render_template("accounting.html",
                           stats=stats, monthly=monthly,
                           unpaid=unpaid, paid_recent=paid_recent,
                           top_customers=top_customers,
                           is_kg=is_kg, now=now,
                           expenses=expenses, expenses_total=expenses_total)


@app.route("/accounting/export-csv")
@login_required
def accounting_export_csv():
    import csv, io
    db = get_db()
    rows = db.execute("""
        SELECT i.number, i.date, i.due_date, i.status,
               c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as netto
        FROM invoices i LEFT JOIN customers c ON c.id=i.customer_id
        WHERE i.status IN ('sent','paid')
        ORDER BY i.date DESC
    """).fetchall()
    db.close()

    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(["Rechnungsnr.", "Datum", "Fällig", "Status", "Kunde", "Firma", "Netto (€)"])
    for r in rows:
        w.writerow([r["number"], r["date"], r["due_date"] or "", r["status"],
                    r["customer_name"] or "", r["customer_company"] or "",
                    f"{r['netto']:.2f}".replace(".", ",")])

    from flask import Response
    return Response(
        "﻿" + buf.getvalue(),  # BOM for Excel
        mimetype="text/csv",
        headers={"Content-Disposition": "attachment; filename=buchhaltung.csv"}
    )


# ── Ausgaben (Expenses) ───────────────────────────────────────────────────────

RECEIPT_DIR = os.path.join(os.path.dirname(__file__), "data", "receipts")
os.makedirs(RECEIPT_DIR, exist_ok=True)

@app.route("/accounting/expenses/new", methods=["POST"])
@login_required
def expense_new():
    date        = request.form.get("date", "").strip()
    category    = request.form.get("category", "Sonstiges").strip()
    description = request.form.get("description", "").strip()
    amount_netto= request.form.get("amount_netto", "0").strip()
    tax_rate    = request.form.get("tax_rate", "19").strip()
    notes       = request.form.get("notes", "").strip()

    if not date or not description:
        flash("Datum und Beschreibung sind Pflichtfelder.", "error")
        return redirect(url_for("accounting"))

    try:
        amount_netto = float(amount_netto)
        tax_rate     = float(tax_rate)
    except ValueError:
        flash("Ungültiger Betrag.", "error")
        return redirect(url_for("accounting"))

    receipt_filename = None
    file = request.files.get("receipt")
    if file and file.filename:
        ext = os.path.splitext(file.filename)[1].lower()
        if ext not in (".pdf", ".jpg", ".jpeg", ".png"):
            flash("Nur PDF, JPG oder PNG erlaubt.", "error")
            return redirect(url_for("accounting"))
        import uuid as _uuid
        safe_name = _uuid.uuid4().hex + ext
        file.save(os.path.join(RECEIPT_DIR, safe_name))
        receipt_filename = safe_name

    db = get_db()
    db.execute(
        "INSERT INTO expenses (date, category, description, amount_netto, tax_rate, receipt_file, notes) VALUES (?,?,?,?,?,?,?)",
        (date, category, description, amount_netto, tax_rate, receipt_filename, notes)
    )
    db.commit()
    db.close()
    flash("Ausgabe gespeichert.", "success")
    return redirect(url_for("accounting"))


@app.route("/accounting/expenses/<int:eid>/delete", methods=["POST"])
@login_required
def expense_delete(eid):
    db = get_db()
    row = db.execute("SELECT receipt_file FROM expenses WHERE id=?", (eid,)).fetchone()
    if row and row["receipt_file"]:
        path = os.path.join(RECEIPT_DIR, row["receipt_file"])
        if os.path.isfile(path):
            os.remove(path)
    db.execute("DELETE FROM expenses WHERE id=?", (eid,))
    db.commit()
    db.close()
    flash("Ausgabe gelöscht.", "success")
    return redirect(url_for("accounting"))


@app.route("/accounting/expenses/<int:eid>/receipt")
@login_required
def expense_receipt(eid):
    db = get_db()
    row = db.execute("SELECT receipt_file FROM expenses WHERE id=?", (eid,)).fetchone()
    db.close()
    if not row or not row["receipt_file"]:
        return "Kein Beleg vorhanden", 404
    filename = row["receipt_file"]
    # Prevent path traversal
    if "/" in filename or "\\" in filename or ".." in filename:
        return "Ungültig", 400
    return send_from_directory(RECEIPT_DIR, filename)


# ── Wiederkehrende Rechnungen ─────────────────────────────────────────────────

def _next_date(current_date_str, interval):
    """Calculate next invoice date based on interval."""
    from dateutil.relativedelta import relativedelta
    d = date.fromisoformat(current_date_str)
    if interval == "monthly":
        return (d + relativedelta(months=1)).isoformat()
    elif interval == "quarterly":
        return (d + relativedelta(months=3)).isoformat()
    elif interval == "yearly":
        return (d + relativedelta(years=1)).isoformat()
    return (d + relativedelta(months=1)).isoformat()


def _create_invoice_from_recurring(db, rec):
    """Create an actual invoice from a recurring template."""
    num = next_invoice_number()
    due = (date.fromisoformat(rec["next_date"]) + __import__('datetime').timedelta(days=14)).isoformat()
    cur = db.execute(
        "INSERT INTO invoices (number, customer_id, date, due_date, status, notes) VALUES (?,?,?,?,?,?)",
        (num, rec["customer_id"], rec["next_date"], due, "draft",
         f"Automatisch erstellt aus Vorlage: {rec['name']}")
    )
    inv_id = cur.lastrowid
    items = db.execute("SELECT * FROM recurring_invoice_items WHERE recurring_id=?", (rec["id"],)).fetchall()
    for it in items:
        db.execute("INSERT INTO invoice_items (invoice_id, description, quantity, unit_price) VALUES (?,?,?,?)",
                   (inv_id, it["description"], it["quantity"], it["unit_price"]))
    # Advance next_date
    new_next = _next_date(rec["next_date"], rec["interval"])
    db.execute("UPDATE recurring_invoices SET next_date=?, last_created=? WHERE id=?",
               (new_next, rec["next_date"], rec["id"]))
    print(f"[RECURRING] Rechnung {num} für Vorlage '{rec['name']}' erstellt (nächste: {new_next})")
    return inv_id


def check_recurring_invoices():
    """Background job: create due recurring invoices."""
    while True:
        try:
            db = get_db()
            today = date.today().isoformat()
            due = db.execute(
                "SELECT * FROM recurring_invoices WHERE status='active' AND next_date<=?", (today,)
            ).fetchall()
            for rec in due:
                _create_invoice_from_recurring(db, rec)
            if due:
                db.commit()
            db.close()
        except Exception as e:
            print(f"[RECURRING] Fehler: {e}")
        time.sleep(3600)  # prüfe stündlich


@app.route("/recurring")
@login_required
def recurring_list():
    db = get_db()
    recs = db.execute("""
        SELECT r.*, c.name as customer_name, c.company as customer_company,
               (SELECT COALESCE(SUM(quantity*unit_price),0) FROM recurring_invoice_items WHERE recurring_id=r.id) as total
        FROM recurring_invoices r
        JOIN customers c ON c.id=r.customer_id
        ORDER BY r.status DESC, r.next_date ASC
    """).fetchall()
    customers = db.execute("SELECT id, name, company FROM customers WHERE status='customer' ORDER BY name").fetchall()
    db.close()
    interval_labels = {"monthly": "Monatlich", "quarterly": "Vierteljährlich", "yearly": "Jährlich"}
    return render_template("recurring.html", recs=recs, customers=customers,
                           interval_labels=interval_labels)


@app.route("/recurring/new", methods=["POST"])
@login_required
def recurring_new():
    customer_id  = request.form.get("customer_id")
    name         = request.form.get("name", "").strip()
    interval     = request.form.get("interval", "monthly")
    start_date   = request.form.get("start_date", date.today().isoformat())
    notes        = request.form.get("notes", "").strip()
    descriptions = request.form.getlist("item_desc")
    quantities   = request.form.getlist("item_qty")
    prices       = request.form.getlist("item_price")

    if not customer_id or not name or not descriptions:
        flash("Pflichtfelder fehlen.", "error")
        return redirect(url_for("recurring_list"))

    db = get_db()
    cur = db.execute(
        "INSERT INTO recurring_invoices (customer_id, name, interval, day_of_month, next_date, notes) VALUES (?,?,?,?,?,?)",
        (customer_id, name, interval, int(start_date.split("-")[2]), start_date, notes)
    )
    rid = cur.lastrowid
    for desc, qty, price in zip(descriptions, quantities, prices):
        desc = desc.strip()
        if not desc:
            continue
        try:
            qty   = float(qty or 1)
            price = float(price or 0)
        except ValueError:
            continue
        db.execute("INSERT INTO recurring_invoice_items (recurring_id, description, quantity, unit_price) VALUES (?,?,?,?)",
                   (rid, desc, qty, price))
    db.commit()
    db.close()
    flash("Wiederkehrende Rechnung erstellt.", "success")
    return redirect(url_for("recurring_list"))


@app.route("/recurring/<int:rid>/toggle", methods=["POST"])
@login_required
def recurring_toggle(rid):
    db = get_db()
    rec = db.execute("SELECT status FROM recurring_invoices WHERE id=?", (rid,)).fetchone()
    if rec:
        new_status = "paused" if rec["status"] == "active" else "active"
        db.execute("UPDATE recurring_invoices SET status=? WHERE id=?", (new_status, rid))
        db.commit()
    db.close()
    return redirect(url_for("recurring_list"))


@app.route("/recurring/<int:rid>/run-now", methods=["POST"])
@login_required
def recurring_run_now(rid):
    db = get_db()
    rec = db.execute("SELECT * FROM recurring_invoices WHERE id=?", (rid,)).fetchone()
    if rec:
        inv_id = _create_invoice_from_recurring(db, rec)
        db.commit()
        db.close()
        flash("Rechnung wurde sofort erstellt.", "success")
        return redirect(url_for("invoice_view", iid=inv_id))
    db.close()
    flash("Vorlage nicht gefunden.", "error")
    return redirect(url_for("recurring_list"))


@app.route("/recurring/<int:rid>/delete", methods=["POST"])
@login_required
def recurring_delete(rid):
    db = get_db()
    db.execute("DELETE FROM recurring_invoices WHERE id=?", (rid,))
    db.commit()
    db.close()
    flash("Vorlage gelöscht.", "success")
    return redirect(url_for("recurring_list"))


# ── Akquise / Lead Pipeline ───────────────────────────────────────────────────

LEAD_STAGES = [
    ("new",        "Neu",              "bg-gray-100 text-gray-600"),
    ("contacted",  "Kontaktiert",      "bg-blue-100 text-blue-700"),
    ("proposal",   "Angebot gesendet", "bg-yellow-100 text-yellow-700"),
    ("negotiation","Verhandlung",      "bg-orange-100 text-orange-700"),
    ("won",        "Gewonnen",         "bg-green-100 text-green-700"),
    ("lost",       "Verloren",         "bg-red-100 text-red-700"),
]
STAGE_KEYS = [s[0] for s in LEAD_STAGES]

LEAD_SOURCES = ["Website", "Empfehlung", "Kaltakquise", "LinkedIn", "Messe", "Promoter", "Sonstiges"]


@app.route("/akquise")
@login_required
def akquise():
    db = get_db()
    leads = db.execute("""
        SELECT l.*,
               (SELECT body FROM lead_activities WHERE lead_id=l.id ORDER BY created_at DESC LIMIT 1) as last_activity,
               (SELECT created_at FROM lead_activities WHERE lead_id=l.id ORDER BY created_at DESC LIMIT 1) as last_activity_at
        FROM leads l ORDER BY l.updated_at DESC
    """).fetchall()

    # KPIs
    total       = len(leads)
    won         = sum(1 for l in leads if l["stage"] == "won")
    active      = sum(1 for l in leads if l["stage"] not in ("won", "lost"))
    pipeline_val= sum(l["deal_value"] or 0 for l in leads if l["stage"] not in ("won", "lost"))
    won_val     = sum(l["deal_value"] or 0 for l in leads if l["stage"] == "won")
    conv_rate   = round(won / total * 100) if total else 0

    # Group by stage for kanban
    from collections import defaultdict
    by_stage = defaultdict(list)
    for l in leads:
        by_stage[l["stage"]].append(dict(l))

    # Overdue follow-ups
    today = date.today().isoformat()
    overdue = [l for l in leads if l["next_followup"] and l["next_followup"] < today
               and l["stage"] not in ("won", "lost")]

    db.close()
    return render_template("akquise.html",
                           leads=leads, by_stage=by_stage,
                           stages=LEAD_STAGES, stage_keys=STAGE_KEYS,
                           sources=LEAD_SOURCES,
                           kpi=dict(total=total, won=won, active=active,
                                    pipeline_val=pipeline_val, won_val=won_val,
                                    conv_rate=conv_rate),
                           overdue=overdue, today=today)


@app.route("/akquise/new", methods=["POST"])
@login_required
def akquise_new():
    db = get_db()
    db.execute("""
        INSERT INTO leads (company, contact_name, contact_email, contact_phone,
                           source, stage, deal_value, notes, next_followup)
        VALUES (?,?,?,?,?,?,?,?,?)
    """, (
        request.form.get("company", "").strip(),
        request.form.get("contact_name", "").strip(),
        request.form.get("contact_email", "").strip(),
        request.form.get("contact_phone", "").strip(),
        request.form.get("source", "Sonstiges"),
        "new",
        float(request.form.get("deal_value") or 0),
        request.form.get("notes", "").strip(),
        request.form.get("next_followup") or None,
    ))
    db.commit()
    db.close()
    flash("Lead erfasst.", "success")
    return redirect(url_for("akquise"))


@app.route("/akquise/<int:lid>")
@login_required
def akquise_detail(lid):
    db = get_db()
    lead = db.execute("SELECT * FROM leads WHERE id=?", (lid,)).fetchone()
    if not lead:
        db.close()
        flash("Lead nicht gefunden.", "error")
        return redirect(url_for("akquise"))
    activities = db.execute(
        "SELECT * FROM lead_activities WHERE lead_id=? ORDER BY created_at DESC", (lid,)
    ).fetchall()
    db.close()
    return render_template("akquise_detail.html", lead=lead, activities=activities,
                           stages=LEAD_STAGES, sources=LEAD_SOURCES, today=date.today().isoformat())


@app.route("/akquise/<int:lid>/stage", methods=["POST"])
@login_required
def akquise_stage(lid):
    new_stage = request.form.get("stage", "")
    if new_stage not in STAGE_KEYS:
        abort(400)
    lost_reason = request.form.get("lost_reason", "").strip()
    db = get_db()
    db.execute("UPDATE leads SET stage=?, lost_reason=?, updated_at=CURRENT_TIMESTAMP WHERE id=?",
               (new_stage, lost_reason if new_stage == "lost" else None, lid))
    # Auto-activity log
    labels = {s[0]: s[1] for s in LEAD_STAGES}
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (?,?,?,?)",
               (lid, "stage", f"Status geändert → {labels.get(new_stage, new_stage)}", session["username"]))
    db.commit()
    db.close()
    return redirect(request.referrer or url_for("akquise_detail", lid=lid))


@app.route("/akquise/<int:lid>/activity", methods=["POST"])
@login_required
def akquise_activity(lid):
    atype = request.form.get("type", "note")
    body  = request.form.get("body", "").strip()
    followup = request.form.get("next_followup") or None
    if not body:
        return redirect(url_for("akquise_detail", lid=lid))
    db = get_db()
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (?,?,?,?)",
               (lid, atype, body, session["username"]))
    db.execute("UPDATE leads SET updated_at=CURRENT_TIMESTAMP, next_followup=? WHERE id=?",
               (followup, lid))
    db.commit()
    db.close()
    return redirect(url_for("akquise_detail", lid=lid))


@app.route("/akquise/<int:lid>/edit", methods=["POST"])
@login_required
def akquise_edit(lid):
    db = get_db()
    db.execute("""UPDATE leads SET company=?, contact_name=?, contact_email=?,
                  contact_phone=?, source=?, deal_value=?, notes=?, next_followup=?,
                  updated_at=CURRENT_TIMESTAMP WHERE id=?""", (
        request.form.get("company", "").strip(),
        request.form.get("contact_name", "").strip(),
        request.form.get("contact_email", "").strip(),
        request.form.get("contact_phone", "").strip(),
        request.form.get("source", "Sonstiges"),
        float(request.form.get("deal_value") or 0),
        request.form.get("notes", "").strip(),
        request.form.get("next_followup") or None,
        lid,
    ))
    db.commit()
    db.close()
    flash("Lead aktualisiert.", "success")
    return redirect(url_for("akquise_detail", lid=lid))


@app.route("/akquise/<int:lid>/delete", methods=["POST"])
@login_required
def akquise_delete(lid):
    db = get_db()
    db.execute("DELETE FROM leads WHERE id=?", (lid,))
    db.commit()
    db.close()
    flash("Lead gelöscht.", "success")
    return redirect(url_for("akquise"))


@app.route("/akquise/<int:lid>/convert", methods=["POST"])
@login_required
def akquise_convert(lid):
    """Convert a won lead into a customer."""
    db = get_db()
    lead = db.execute("SELECT * FROM leads WHERE id=?", (lid,)).fetchone()
    if not lead:
        db.close()
        flash("Lead nicht gefunden.", "error")
        return redirect(url_for("akquise"))
    cnum = next_customer_number(db)
    db.execute("""INSERT INTO customers (customer_number, name, company, email, phone, source, status)
                  VALUES (?,?,?,?,?,?,?)""", (
        cnum,
        lead["contact_name"],
        lead["company"] or "",
        lead["contact_email"] or "",
        lead["contact_phone"] or "",
        lead["source"] or "",
        "customer",
    ))
    db.execute("UPDATE leads SET stage='won', updated_at=CURRENT_TIMESTAMP WHERE id=?", (lid,))
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (?,?,?,?)",
               (lid, "converted", f"In Kunde umgewandelt (Kundennr. {cnum})", session["username"]))
    db.commit()
    db.close()
    flash(f"Lead als Kunde angelegt ({cnum}).", "success")
    return redirect(url_for("akquise"))


# ── Init ──────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    init_db()
    db = get_db()
    existing = db.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    if existing == 0:
        db.execute("INSERT INTO users (username, password_hash) VALUES (?,?)",
                   ("admin", generate_password_hash("admin")))
        db.commit()
        print("Default login: admin / admin")
    db.close()
    t = threading.Thread(target=imap_loop, daemon=True)
    t.start()
    t2 = threading.Thread(target=check_recurring_invoices, daemon=True)
    t2.start()
    print("[RECURRING] Hintergrund-Job gestartet (stündliche Prüfung)")
    app.run(host="0.0.0.0", port=5000, debug=False)
