import os
import re
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
import logging
import traceback
from logging.handlers import RotatingFileHandler
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
    SESSION_COOKIE_SECURE    = True,
    PERMANENT_SESSION_LIFETIME = 2 * 3600,  # 8 hours
    MAX_CONTENT_LENGTH       = 20 * 1024 * 1024,  # 20 MB upload limit
)

# Password encryption for DB-stored secrets (SMTP/IMAP)
def _fernet():
    """Derive a Fernet key from SECRET_KEY (32-byte SHA-256, base64url-encoded)."""
    import base64
    raw = hashlib.sha256(app.secret_key.encode()).digest()
    return base64.urlsafe_b64encode(raw)

def encrypt_secret(plaintext: str) -> str:
    if not plaintext:
        return ""
    from cryptography.fernet import Fernet
    return "fernet:" + Fernet(_fernet()).encrypt(plaintext.encode()).decode()

def decrypt_secret(ciphertext: str) -> str:
    if not ciphertext:
        return ""
    if not ciphertext.startswith("fernet:"):
        # Altes Format (XOR/enc:) oder unbekannt — leer zurückgeben
        return ""
    from cryptography.fernet import Fernet
    return Fernet(_fernet()).decrypt(ciphertext[7:].encode()).decode()

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


@app.template_filter("fmtdt")
def fmtdt(value, fmt="%Y-%m-%d %H:%M"):
    """Safely format a timestamp coming from the DB, whether psycopg2 hands us
    a datetime object (the normal case) or a plain string."""
    if not value:
        return "–"
    if hasattr(value, "strftime"):
        return value.strftime(fmt)
    return str(value)[:16].replace("T", " ")


@app.template_filter("fmtdate")
def fmtdate(value):
    """Format a plain ISO date (YYYY-MM-DD, string or date/datetime) as TT.MM.JJJJ."""
    if not value:
        return "–"
    if hasattr(value, "strftime"):
        return value.strftime("%d.%m.%Y")
    try:
        return date.fromisoformat(str(value)[:10]).strftime("%d.%m.%Y")
    except Exception:
        return str(value)


def log_activity(db, action, entity_type, entity_id=None, entity_label=None, details=None):
    """Record who changed what, for the activity/audit log. Fails silently if
    the audit table isn't there yet (e.g. during first-ever request)."""
    try:
        db.execute(
            "INSERT INTO audit_log (user_id, username, action, entity_type, entity_id, entity_label, details) "
            "VALUES (%s,%s,%s,%s,%s,%s,%s)",
            (session.get("user_id"), session.get("username", "system"), action,
             entity_type, entity_id, entity_label, details),
        )
    except Exception:
        pass

# ── Logging ───────────────────────────────────────────────────────────────────
_log_path = os.path.join(os.path.dirname(__file__), "data", "app.log")
_file_handler = RotatingFileHandler(_log_path, maxBytes=5*1024*1024, backupCount=3, encoding="utf-8")
_file_handler.setLevel(logging.ERROR)
_file_handler.setFormatter(logging.Formatter(
    "[%(asctime)s] %(levelname)s in %(module)s: %(message)s"
))
app.logger.addHandler(_file_handler)
app.logger.setLevel(logging.ERROR)


@app.errorhandler(500)
def handle_500(e):
    tb = traceback.format_exc()
    req_info = f"{request.method} {request.url} | User: {session.get('username', 'anonym')}"
    app.logger.error(f"{req_info}\n{tb}")
    try:
        cfg = get_settings(get_db())
        notify = cfg.get("error_notify_email", "").strip()
        if notify and cfg.get("smtp_host", "").strip():
            send_smtp_email(
                notify,
                f"[tkToolkit] Fehler: {request.path}",
                f"Zeitpunkt: {datetime.now().strftime('%d.%m.%Y %H:%M:%S')}\n"
                f"Request: {req_info}\n\n{tb}",
                cfg,
            )
    except Exception:
        pass
    return render_template("500.html"), 500

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
    urow = db2.execute("SELECT avatar FROM users WHERE id=%s", (session["user_id"],)).fetchone()
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
        if time.time() - last_active > 2 * 3600:
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
        if session.get("role") != "admin":
            flash("Kein Zugriff – nur für Administratoren.", "error")
            return redirect(url_for("dashboard"))
        return f(*args, **kwargs)
    return decorated


def _calc_commission_for_invoice(db, invoice_id):
    """Check if this invoice triggers a promoter commission. Creates entry if yes."""
    inv = db.execute("SELECT * FROM invoices WHERE id=%s", (invoice_id,)).fetchone()
    if not inv or not inv["customer_id"]:
        return
    inv_date = inv["date"]
    assignments = db.execute("""
        SELECT * FROM promoter_assignments
        WHERE customer_id=%s
          AND start_date <= %s
          AND (end_date IS NULL OR end_date >= %s)
    """, (inv["customer_id"], inv_date, inv_date)).fetchall()
    for a in assignments:
        # avoid duplicate commission for same invoice+assignment
        exists = db.execute(
            "SELECT id FROM promoter_commissions WHERE assignment_id=%s AND invoice_id=%s",
            (a["id"], invoice_id)).fetchone()
        if exists:
            continue
        total = db.execute(
            "SELECT COALESCE(SUM(quantity*unit_price),0) as t FROM invoice_items WHERE invoice_id=%s",
            (invoice_id,)).fetchone()["t"]
        commission = round(total * a["commission_pct"] / 100, 2)
        db.execute("""
            INSERT INTO promoter_commissions (assignment_id, invoice_id, invoice_total, commission_pct, amount)
            VALUES (%s,%s,%s,%s,%s)
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
        db.execute("INSERT INTO feed_messages (user_id, username, body, attachment) VALUES (%s,%s,%s,%s)",
                   (session["user_id"], session["username"], body or "", attachment))
        # Detect @mentions and notify each mentioned user
        if body:
            sender = session.get("display_name") or session.get("username")
            for uname in set(re.findall(r'@(\w+)', body)):
                user = db.execute("SELECT id FROM users WHERE username=%s", (uname,)).fetchone()
                if user and user["id"] != session["user_id"]:
                    preview = body[:80] + ("…" if len(body) > 80 else "")
                    db.execute(
                        "INSERT INTO notifications (type, title, body, link, target_user_id) VALUES (%s,%s,%s,%s,%s)",
                        ("mention", f"{sender} hat dich erwähnt", f'"{preview}"', None, user["id"]))
        db.commit()
        db.close()
    return redirect(request.referrer or url_for("dashboard"))


@app.route("/feed/message/<int:mid>/edit", methods=["POST"])
@login_required
def feed_message_edit(mid):
    body = request.form.get("body", "").strip()
    if body:
        db = get_db()
        msg = db.execute("SELECT user_id FROM feed_messages WHERE id=%s", (mid,)).fetchone()
        if msg and msg["user_id"] == session["user_id"]:
            db.execute("UPDATE feed_messages SET body=%s WHERE id=%s", (body, mid))
            db.commit()
        db.close()
    return redirect(request.referrer or url_for("dashboard"))


@app.route("/feed/message/<int:mid>/delete", methods=["POST"])
@login_required
def feed_message_delete(mid):
    db = get_db()
    msg = db.execute("SELECT user_id FROM feed_messages WHERE id=%s", (mid,)).fetchone()
    if msg and msg["user_id"] == session["user_id"]:
        db.execute("DELETE FROM feed_messages WHERE id=%s", (mid,))
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
    result = []
    for r in rows:
        d = dict(r)
        if isinstance(d.get("created_at"), datetime):
            d["created_at"] = d["created_at"].strftime("%Y-%m-%dT%H:%M:%S")
        else:
            d["created_at"] = str(d["created_at"])[:19].replace(" ", "T")
        result.append(d)
    return jsonify(result)


# ── Auth ──────────────────────────────────────────────────────────────────────

def _no_users_exist():
    db = get_db()
    count = db.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    db.close()
    return count == 0


@app.route("/setup", methods=["GET", "POST"])
def setup():
    if not _no_users_exist():
        return redirect(url_for("login"))
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        display  = request.form.get("display_name", "").strip()
        pw       = request.form.get("password", "")
        pw2      = request.form.get("password2", "")
        if not username or not pw:
            return render_template("setup.html", error="Benutzername und Passwort erforderlich.")
        if pw != pw2:
            return render_template("setup.html", error="Passwörter stimmen nicht überein.")
        if not _no_users_exist():
            return redirect(url_for("login"))
        db = get_db()
        phash = generate_password_hash(pw)
        db.execute(
            "INSERT INTO users (username, password_hash, display_name, role) VALUES (%s,%s,%s,%s)",
            (username, phash, display or username, "admin"))
        db.commit()
        db.close()
        flash("Administrator-Konto angelegt. Bitte anmelden.", "success")
        return redirect(url_for("login"))
    return render_template("setup.html", error=None)


@app.route("/login", methods=["GET", "POST"])
def login():
    if _no_users_exist():
        return redirect(url_for("setup"))
    if request.method == "POST":
        ip = request.remote_addr or "unknown"
        if _check_rate_limit(ip):
            flash("Zu viele Anmeldeversuche. Bitte 5 Minuten warten.", "error")
            return render_template("login.html")
        db = get_db()
        user = db.execute("SELECT * FROM users WHERE username=%s", (request.form.get("username", ""),)).fetchone()
        db.close()
        if user and check_password_hash(user["password_hash"], request.form.get("password", "")):
            _clear_attempts(ip)
            session["user_id"] = user["id"]
            session["username"] = user["username"]
            session["display_name"] = user["display_name"] or user["username"]
            session["role"] = user["role"] or "admin"
            dest = url_for("dashboard")
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
        "invoices_open_amount": db.execute("""
            SELECT COALESCE(SUM(ii.quantity * ii.unit_price),0)
            FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
            WHERE i.status = 'sent'
        """).fetchone()[0],
        "revenue_month":   db.execute("""
            SELECT COALESCE(SUM(ii.quantity * ii.unit_price),0)
            FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
            WHERE i.status IN ('sent','paid') AND TO_CHAR(i.date::date, 'YYYY-MM') = TO_CHAR(CURRENT_DATE, 'YYYY-MM')
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
    overdue_invoices = db.execute("""
        SELECT i.id, i.number, i.due_date, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total,
               (CURRENT_DATE - i.due_date::date) as overdue_days
        FROM invoices i LEFT JOIN customers c ON i.customer_id = c.id
        WHERE i.status = 'sent' AND i.due_date IS NOT NULL AND i.due_date != '' AND i.due_date::date < CURRENT_DATE
        ORDER BY i.due_date ASC
    """).fetchall()
    from datetime import datetime
    current_year = datetime.now().year
    revenue_rows = db.execute("""
        SELECT EXTRACT(MONTH FROM i.date::date) as mon,
               COALESCE(SUM(ii.quantity * ii.unit_price), 0) as total
        FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
        WHERE i.status IN ('sent','paid')
          AND EXTRACT(YEAR FROM i.date::date) = %s
        GROUP BY 1 ORDER BY 1
    """, (current_year,)).fetchall()
    month_names = ['Jan','Feb','Mär','Apr','Mai','Jun','Jul','Aug','Sep','Okt','Nov','Dez']
    rev_by_month = {int(r['mon']): float(r['total']) for r in revenue_rows}
    all_months = [{'label': month_names[m-1], 'total': rev_by_month.get(m, 0.0)} for m in range(1, 13)]
    upcoming_recurring = db.execute("""
        SELECT r.id, r.name, r.next_date, r.interval, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM recurring_invoice_items WHERE recurring_id=r.id),0) as total
        FROM recurring_invoices r LEFT JOIN customers c ON r.customer_id = c.id
        WHERE r.status = 'active' AND r.next_date::date <= CURRENT_DATE + INTERVAL '14 days'
        ORDER BY r.next_date ASC LIMIT 5
    """).fetchall()

    revenue_month_prev = db.execute("""
        SELECT COALESCE(SUM(ii.quantity * ii.unit_price),0)
        FROM invoices i JOIN invoice_items ii ON ii.invoice_id = i.id
        WHERE i.status IN ('sent','paid')
          AND TO_CHAR(i.date::date, 'YYYY-MM') = TO_CHAR(CURRENT_DATE - INTERVAL '1 month', 'YYYY-MM')
    """).fetchone()[0]

    top_customers = db.execute("""
        SELECT c.name, c.company, SUM(ii.quantity*ii.unit_price) as total
        FROM invoices i
        JOIN invoice_items ii ON ii.invoice_id=i.id
        JOIN customers c ON c.id=i.customer_id
        WHERE i.status IN ('sent','paid')
        GROUP BY c.id ORDER BY total DESC LIMIT 5
    """).fetchall()
    top_customers_max = max([c["total"] for c in top_customers], default=0)

    db.close()
    return render_template("dashboard.html", stats=stats,
                           recent_tickets=recent_tickets, recent_invoices=recent_invoices,
                           overdue_invoices=overdue_invoices, revenue_months=all_months,
                           upcoming_recurring=upcoming_recurring,
                           revenue_month_prev=revenue_month_prev,
                           top_customers=top_customers, top_customers_max=top_customers_max,
                           current_year=current_year, now_hour=datetime.now().hour)


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
        query += " AND (name LIKE %s OR company LIKE %s OR email LIKE %s)"
        params += [f"%{q}%", f"%{q}%", f"%{q}%"]
    if status:
        query += " AND status=%s"
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
        new_id = db.execute("""INSERT INTO customers
            (customer_number,company,legal_form,name,email,phone,website,
             street,zip,city,country,tax_id,payment_terms,
             contact_person,contact_position,contact_email,contact_phone,contact_mobile,
             contract_type,support_level,contract_start,contract_end,monthly_rate,
             num_workstations,num_servers,it_notes,source,notes,status)
            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s) RETURNING id""", fields).fetchone()
        log_activity(db, "erstellt", "Kunde", new_id["id"], fields[3])
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
    customer = db.execute("SELECT * FROM customers WHERE id=%s", (cid,)).fetchone()
    if request.method == "POST":
        fields = _customer_fields(request.form)
        db.execute("""UPDATE customers SET
            customer_number=%s,company=%s,legal_form=%s,name=%s,email=%s,phone=%s,website=%s,
            street=%s,zip=%s,city=%s,country=%s,tax_id=%s,payment_terms=%s,
            contact_person=%s,contact_position=%s,contact_email=%s,contact_phone=%s,contact_mobile=%s,
            contract_type=%s,support_level=%s,contract_start=%s,contract_end=%s,monthly_rate=%s,
            num_workstations=%s,num_servers=%s,it_notes=%s,source=%s,notes=%s,status=%s
            WHERE id=%s""", (*fields, cid))
        log_activity(db, "bearbeitet", "Kunde", cid, fields[3])
        db.commit()
        db.close()
        flash("Kunde gespeichert", "success")
        return redirect(url_for("customers"))
    db.close()
    return render_template("customer_form.html", customer=customer, kd_nr=None)


@app.route("/customers/<int:cid>")
@login_required
def customer_detail(cid):
    db = get_db()
    customer = db.execute("SELECT * FROM customers WHERE id=%s", (cid,)).fetchone()
    if not customer:
        db.close()
        flash("Kunde nicht gefunden", "error")
        return redirect(url_for("customers"))
    tickets = db.execute("""
        SELECT * FROM tickets WHERE customer_id=%s ORDER BY
        CASE status WHEN 'open' THEN 1 WHEN 'in_progress' THEN 2 ELSE 3 END,
        CASE priority WHEN 'high' THEN 1 WHEN 'medium' THEN 2 ELSE 3 END,
        created_at DESC
    """, (cid,)).fetchall()
    invoices = db.execute("""
        SELECT i.*, COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total
        FROM invoices i WHERE i.customer_id=%s ORDER BY i.date DESC
    """, (cid,)).fetchall()
    revenue_total = db.execute("""
        SELECT COALESCE(SUM(ii.quantity*ii.unit_price),0)
        FROM invoices i JOIN invoice_items ii ON ii.invoice_id=i.id
        WHERE i.customer_id=%s AND i.status IN ('sent','paid')
    """, (cid,)).fetchone()[0]
    contacts = db.execute(
        "SELECT * FROM customer_contacts WHERE customer_id=%s ORDER BY created_at ASC", (cid,)
    ).fetchall()
    db.close()
    return render_template("customer_detail.html", customer=customer,
                           tickets=tickets, invoices=invoices,
                           revenue_total=revenue_total, contacts=contacts)


@app.route("/customers/<int:cid>/status", methods=["POST"])
@login_required
def customer_status(cid):
    new_status = request.form.get("status")
    if new_status not in ("lead", "customer", "inactive"):
        flash("Ungültiger Status", "error")
        return redirect(url_for("customers"))
    db = get_db()
    cust = db.execute("SELECT name FROM customers WHERE id=%s", (cid,)).fetchone()
    db.execute("UPDATE customers SET status=%s WHERE id=%s", (new_status, cid))
    log_activity(db, "Status geändert", "Kunde", cid, cust["name"] if cust else None, f"neuer Status: {new_status}")
    db.commit()
    db.close()
    return redirect(request.referrer or url_for("customers"))


@app.route("/customers/<int:cid>/contacts/add", methods=["POST"])
@login_required
def customer_contact_add(cid):
    db = get_db()
    db.execute("""INSERT INTO customer_contacts (customer_id, name, position, email, phone, mobile, notes)
                  VALUES (%s,%s,%s,%s,%s,%s,%s)""",
               (cid, request.form.get("name"), request.form.get("position"),
                request.form.get("email"), request.form.get("phone"),
                request.form.get("mobile"), request.form.get("notes")))
    db.commit()
    db.close()
    flash("Ansprechpartner hinzugefügt", "success")
    return redirect(url_for("customer_detail", cid=cid))


@app.route("/customers/<int:cid>/contacts/<int:ctid>/delete", methods=["POST"])
@login_required
def customer_contact_delete(cid, ctid):
    db = get_db()
    db.execute("DELETE FROM customer_contacts WHERE id=%s AND customer_id=%s", (ctid, cid))
    db.commit()
    db.close()
    return redirect(url_for("customer_detail", cid=cid))


@app.route("/customers/<int:cid>/delete", methods=["POST"])
@login_required
def customer_delete(cid):
    db = get_db()
    cust = db.execute("SELECT name FROM customers WHERE id=%s", (cid,)).fetchone()
    inv_count = db.execute(
        "SELECT COUNT(*) FROM invoices WHERE customer_id=%s AND status IN ('sent','paid')", (cid,)
    ).fetchone()[0]
    if inv_count > 0:
        db.close()
        flash(f"Kunde kann nicht gelöscht werden – es existieren {inv_count} gesendete/bezahlte Rechnung(en). Setze den Kunden stattdessen auf 'Inaktiv'.", "error")
        return redirect(url_for("customer_detail", cid=cid))
    # delete only draft invoices
    draft_ids = [r[0] for r in db.execute(
        "SELECT id FROM invoices WHERE customer_id=%s AND status='draft'", (cid,)).fetchall()]
    for iid in draft_ids:
        db.execute("DELETE FROM invoice_items WHERE invoice_id=%s", (iid,))
    if draft_ids:
        db.execute("DELETE FROM invoices WHERE id=ANY(%s)", (draft_ids,))
    db.execute("UPDATE tickets SET customer_id=NULL WHERE customer_id=%s", (cid,))
    db.execute("DELETE FROM outreach WHERE customer_id=%s", (cid,))
    db.execute("DELETE FROM customers WHERE id=%s", (cid,))
    log_activity(db, "gelöscht", "Kunde", cid, cust["name"] if cust else None)
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
        inv_id = db.execute("""INSERT INTO invoices (number, customer_id, date, due_date, status, notes)
                      VALUES (%s,%s,%s,%s,%s,%s) RETURNING id""",
                   (number, request.form["customer_id"], request.form["date"],
                    request.form["due_date"], request.form["status"], request.form["notes"])).fetchone()["id"]
        descs = request.form.getlist("desc[]")
        qtys = request.form.getlist("qty[]")
        prices = request.form.getlist("price[]")
        for desc, qty, price in zip(descs, qtys, prices):
            if desc.strip():
                db.execute("INSERT INTO invoice_items (invoice_id, description, quantity, unit_price) VALUES (%s,%s,%s,%s)",
                           (inv_id, desc, float(qty), float(price)))
        log_activity(db, "erstellt", "Rechnung", inv_id, number)
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
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=%s""", (iid,)).fetchone()
    items = db.execute("SELECT * FROM invoice_items WHERE invoice_id=%s", (iid,)).fetchall()
    total = sum(it["quantity"] * it["unit_price"] for it in items)
    email_log = db.execute("SELECT * FROM invoice_emails WHERE invoice_id=%s ORDER BY sent_at DESC", (iid,)).fetchall()
    cfg = get_settings(db)
    db.close()
    return render_template("invoice_view.html", invoice=invoice, items=items, total=total,
                           email_log=email_log, cfg=cfg)


def generate_invoice_pdf_bytes(iid, db):
    from io import BytesIO
    from xhtml2pdf import pisa
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.company as customer_company,
                                   c.street, c.zip, c.city, c.email, c.tax_id as customer_tax_id
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=%s""", (iid,)).fetchone()
    items   = db.execute("SELECT * FROM invoice_items WHERE invoice_id=%s", (iid,)).fetchall()
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
    invoice = db.execute("SELECT number FROM invoices WHERE id=%s", (iid,)).fetchone()
    if not invoice:
        db.close()
        abort(404)
    try:
        pdf = generate_invoice_pdf_bytes(iid, db)
    finally:
        db.close()
    from flask import Response
    disposition = "inline" if request.args.get("inline") else "attachment"
    return Response(pdf, mimetype="application/pdf",
                    headers={"Content-Disposition": f'{disposition}; filename="Rechnung_{invoice["number"]}.pdf"'})


@app.route("/invoices/<int:iid>/send-email", methods=["POST"])
@login_required
def invoice_send_email(iid):
    db = get_db()
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.email as customer_email
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=%s""", (iid,)).fetchone()
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
        db.execute("INSERT INTO invoice_emails (invoice_id, to_addr, subject, sent_by) VALUES (%s,%s,%s,%s)",
                   (iid, to_addr, subject, session["username"]))
        if invoice["status"] == "draft":
            db.execute("UPDATE invoices SET status='sent' WHERE id=%s", (iid,))
        _calc_commission_for_invoice(db, iid)
        db.commit()
        flash(f"Rechnung als PDF an {to_addr} gesendet ✓", "success")
    except Exception as e:
        flash(f"E-Mail-Fehler: {e}", "error")
    db.close()
    return redirect(url_for("invoice_view", iid=iid))


# ------------------------------------------------------------------ Mahnwesen

#  Stufe -> (Titel, Standard-Mahngebuehr, Zahlungsfrist in Tagen)
DUNNING_LEVELS = {
    1: ("Zahlungserinnerung", 0.0, 14),
    2: ("1. Mahnung", 5.0, 10),
    3: ("2. Mahnung", 10.0, 7),
}


def _smtp_send_pdf(cfg, to_addr, subject, body, pdf_bytes, pdf_name):
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
    pdf_part = MIMEBase("application", "pdf")
    pdf_part.set_payload(pdf_bytes)
    email_encoders.encode_base64(pdf_part)
    pdf_part.add_header("Content-Disposition", f'attachment; filename="{pdf_name}"')
    msg.attach(pdf_part)
    if port == 465:
        with smtplib.SMTP_SSL(host, port, timeout=20) as s:
            s.login(user, pw)
            s.sendmail(from_email, to_addr, msg.as_string())
    else:
        with smtplib.SMTP(host, port, timeout=20) as s:
            s.ehlo(); s.starttls(); s.ehlo()
            s.login(user, pw)
            s.sendmail(from_email, to_addr, msg.as_string())


def _dunning_context(iid, level, db):
    invoice = db.execute("""SELECT i.*, c.name as customer_name, c.company as customer_company,
                                   c.street, c.zip, c.city, c.email as customer_email, c.tax_id as customer_tax_id
                            FROM invoices i JOIN customers c ON i.customer_id=c.id WHERE i.id=%s""", (iid,)).fetchone()
    if not invoice:
        return None
    items = db.execute("SELECT * FROM invoice_items WHERE invoice_id=%s", (iid,)).fetchall()
    total = sum(it["quantity"] * it["unit_price"] for it in items)
    cfg   = get_settings(db)
    kleingewerbe = cfg.get("company_kleingewerbe") == "1"
    grand_total  = total if kleingewerbe else total * 1.19
    title, fee, days = DUNNING_LEVELS[level]
    deadline = (date.today() + timedelta(days=days)).strftime("%d.%m.%Y")
    return {"invoice": invoice, "total": grand_total, "cfg": cfg, "level": level,
            "title": title, "fee": fee, "deadline": deadline,
            "amount_due": grand_total + fee}


def generate_dunning_pdf_bytes(iid, level, db):
    from io import BytesIO
    from xhtml2pdf import pisa
    ctx = _dunning_context(iid, level, db)
    data_dir = os.path.join(os.path.dirname(__file__), "data")
    html_str = render_template("dunning_pdf.html", doc_store=data_dir, **ctx)
    buf = BytesIO()
    pisa.CreatePDF(html_str.encode("utf-8"), dest=buf)
    return buf.getvalue()


@app.route("/mahnwesen")
@login_required
def dunning_list():
    db = get_db()
    rows = db.execute("""
        SELECT i.id, i.number, i.date, i.due_date, c.name as customer_name, c.company, c.email as customer_email,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total,
               (CURRENT_DATE - i.due_date::date) as overdue_days,
               COALESCE((SELECT MAX(level) FROM dunning_notices WHERE invoice_id=i.id),0) as dunning_level,
               (SELECT MAX(sent_at) FROM dunning_notices WHERE invoice_id=i.id) as last_dunning
        FROM invoices i JOIN customers c ON i.customer_id=c.id
        WHERE i.status = 'sent' AND i.due_date IS NOT NULL AND i.due_date != '' AND i.due_date::date < CURRENT_DATE
        ORDER BY overdue_days DESC
    """).fetchall()
    history = db.execute("""
        SELECT d.*, i.number, c.name as customer_name, c.company
        FROM dunning_notices d JOIN invoices i ON d.invoice_id=i.id JOIN customers c ON i.customer_id=c.id
        ORDER BY d.sent_at DESC LIMIT 50
    """).fetchall()
    cfg = get_settings(db)
    db.close()
    return render_template("dunning.html", invoices=rows, history=history,
                           levels=DUNNING_LEVELS, cfg=cfg)


@app.route("/invoices/<int:iid>/dunning/<int:level>/pdf")
@login_required
def dunning_pdf(iid, level):
    if level not in DUNNING_LEVELS:
        abort(404)
    db = get_db()
    invoice = db.execute("SELECT number FROM invoices WHERE id=%s", (iid,)).fetchone()
    if not invoice:
        db.close()
        abort(404)
    try:
        pdf = generate_dunning_pdf_bytes(iid, level, db)
    finally:
        db.close()
    from flask import Response
    fname = f"{DUNNING_LEVELS[level][0].replace(' ', '_').replace('.', '')}_{invoice['number']}.pdf"
    disposition = "inline" if request.args.get("inline") else "attachment"
    return Response(pdf, mimetype="application/pdf",
                    headers={"Content-Disposition": f'{disposition}; filename="{fname}"'})


@app.route("/invoices/<int:iid>/dunning/<int:level>/send", methods=["POST"])
@login_required
def dunning_send(iid, level):
    if level not in DUNNING_LEVELS:
        abort(404)
    db = get_db()
    ctx = _dunning_context(iid, level, db)
    if not ctx:
        db.close()
        abort(404)
    invoice = ctx["invoice"]
    title   = ctx["title"]
    via     = "manual"
    to_addr = (invoice["customer_email"] or "").strip()
    send_mail = request.form.get("send_email") == "1" and to_addr
    try:
        if send_mail:
            body = (f"Sehr geehrte Damen und Herren,\n\n"
                    f"zur Rechnung {invoice['number']} vom {invoice['date']} konnten wir noch keinen "
                    f"Zahlungseingang feststellen. Details entnehmen Sie bitte dem Anhang.\n\n"
                    f"Bitte begleichen Sie den offenen Betrag von {ctx['amount_due']:.2f} EUR "
                    f"bis zum {ctx['deadline']}.\n\n"
                    f"Sollte sich Ihre Zahlung mit diesem Schreiben überschnitten haben, "
                    f"betrachten Sie es bitte als gegenstandslos.\n\n"
                    f"Mit freundlichen Grüßen\n{ctx['cfg'].get('company_name','')}")
            pdf_bytes = generate_dunning_pdf_bytes(iid, level, db)
            fname = f"{title.replace(' ', '_').replace('.', '')}_{invoice['number']}.pdf"
            _smtp_send_pdf(ctx["cfg"], to_addr, f"{title} zur Rechnung {invoice['number']}",
                           body, pdf_bytes, fname)
            via = "email"
        db.execute("INSERT INTO dunning_notices (invoice_id, level, fee, deadline, sent_by, sent_via) VALUES (%s,%s,%s,%s,%s,%s)",
                   (iid, level, ctx["fee"], ctx["deadline"], session["username"], via))
        log_activity(db, "erstellt", "Mahnung", iid, invoice["number"], f"{title}" + (f" per E-Mail an {to_addr}" if via == "email" else ""))
        db.commit()
        if via == "email":
            flash(f"{title} per E-Mail an {to_addr} gesendet ✓", "success")
        else:
            flash(f"{title} vermerkt — PDF kann heruntergeladen werden", "success")
    except Exception as e:
        flash(f"Fehler beim Mahnversand: {e}", "error")
    db.close()
    return redirect(url_for("dunning_list"))


#  Sobald eine Rechnung tatsaechlich versendet oder bezahlt wurde, gilt sie als
#  ausgestellt und darf laut GoBD nicht mehr geloescht oder "rueckgaengig" auf
#  Entwurf gesetzt werden (fortlaufende, lueckenlose Rechnungsnummerierung).
#  Stattdessen gibt es "Stornieren": Nummer und Datensatz bleiben erhalten,
#  die Rechnung wird nur als ungueltig markiert.
_ISSUED_STATUSES = ("sent", "paid")

@app.route("/invoices/<int:iid>/status/<status>", methods=["POST"])
@login_required
def invoice_status(iid, status):
    db = get_db()
    current = db.execute("SELECT status, number FROM invoices WHERE id=%s", (iid,)).fetchone()
    if not current:
        db.close()
        abort(404)

    if current["status"] in _ISSUED_STATUSES and status == "draft":
        flash("Bereits versendete/bezahlte Rechnungen koennen nicht mehr auf Entwurf zurueckgesetzt werden.", "error")
        db.close()
        return redirect(url_for("invoice_view", iid=iid))

    db.execute("UPDATE invoices SET status=%s WHERE id=%s", (status, iid))
    if status in _ISSUED_STATUSES:
        _calc_commission_for_invoice(db, iid)
    log_activity(db, "Status geändert", "Rechnung", iid, current["number"], f"neuer Status: {status}")
    db.commit()
    db.close()
    return redirect(url_for("invoice_view", iid=iid))


@app.route("/invoices/<int:iid>/cancel", methods=["POST"])
@admin_required
def invoice_cancel(iid):
    db = get_db()
    invoice = db.execute("SELECT status, number FROM invoices WHERE id=%s", (iid,)).fetchone()
    if not invoice:
        db.close()
        abort(404)
    if invoice["status"] not in _ISSUED_STATUSES:
        db.close()
        flash("Nur versendete/bezahlte Rechnungen koennen storniert werden.", "error")
        return redirect(url_for("invoice_view", iid=iid))
    db.execute("UPDATE invoices SET status='cancelled' WHERE id=%s", (iid,))
    log_activity(db, "storniert", "Rechnung", iid, invoice["number"])
    db.commit()
    db.close()
    flash("Rechnung storniert. Nummer und Datensatz bleiben zu Dokumentationszwecken erhalten.", "success")
    return redirect(url_for("invoice_view", iid=iid))


@app.route("/invoices/<int:iid>/delete", methods=["POST"])
@login_required
def invoice_delete(iid):
    db = get_db()
    invoice = db.execute("SELECT status, number FROM invoices WHERE id=%s", (iid,)).fetchone()
    if not invoice:
        db.close()
        abort(404)
    if invoice["status"] in _ISSUED_STATUSES:
        db.close()
        flash(f"Rechnung {invoice['number']} wurde bereits versendet/bezahlt und darf laut GoBD nicht "
              f"geloescht werden. Nutze stattdessen 'Stornieren'.", "error")
        return redirect(url_for("invoices"))
    db.execute("DELETE FROM invoices WHERE id=%s", (iid,))
    log_activity(db, "gelöscht", "Rechnung", iid, invoice["number"])
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
    db.execute("INSERT INTO settings (key,value) VALUES (%s,%s) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
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
        query += " AND t.status=%s"
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
        new_id = db.execute("""INSERT INTO tickets (title, description, customer_id, priority, status)
                      VALUES (%s,%s,%s,%s,%s) RETURNING id""",
                   (request.form["title"], request.form["description"],
                    request.form["customer_id"] or None,
                    request.form["priority"], request.form["status"])).fetchone()["id"]
        log_activity(db, "erstellt", "Ticket", new_id, request.form["title"])
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
    ticket = db.execute("SELECT * FROM tickets WHERE id=%s", (tid,)).fetchone()
    if request.method == "POST":
        db.execute("""UPDATE tickets SET title=%s, description=%s, customer_id=%s, priority=%s, status=%s,
                      updated_at=CURRENT_TIMESTAMP WHERE id=%s""",
                   (request.form["title"], request.form["description"],
                    request.form["customer_id"] or None,
                    request.form["priority"], request.form["status"], tid))
        log_activity(db, "bearbeitet", "Ticket", tid, request.form["title"], f"Status: {request.form['status']}")
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
    ticket = db.execute("SELECT title FROM tickets WHERE id=%s", (tid,)).fetchone()
    db.execute("DELETE FROM tickets WHERE id=%s", (tid,))
    log_activity(db, "gelöscht", "Ticket", tid, ticket["title"] if ticket else None)
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
        WHERE t.id=%s""", (tid,)).fetchone()
    if not ticket:
        db.close()
        flash("Ticket nicht gefunden", "error")
        return redirect(url_for("tickets"))
    updates = db.execute(
        "SELECT * FROM ticket_updates WHERE ticket_id=%s ORDER BY created_at ASC", (tid,)
    ).fetchall()
    customers = db.execute("SELECT id, name, company, email FROM customers ORDER BY name").fetchall()
    db.execute("UPDATE tickets SET is_read=1 WHERE id=%s", (tid,))
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
        old = db.execute("SELECT * FROM tickets WHERE id=%s", (tid,)).fetchone()
        if old and old["status"] != new_status:
            labels = {"open": "Offen", "in_progress": "In Arbeit", "closed": "Gelöst"}
            status_note = f"Status geändert: {labels.get(old['status'], old['status'])} → {labels.get(new_status, new_status)}"
            db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                          VALUES (%s,%s,%s,%s,%s)""",
                       (tid, session["user_id"], session["username"], status_note, "status_change"))

            # auto-email customer when ticket is closed
            if new_status == "closed" and old:
                cust = db.execute(
                    "SELECT c.email, c.name FROM customers c WHERE c.id=%s",
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
                                      VALUES (%s,%s,%s,%s,%s)""",
                                   (tid, session["user_id"], session["username"],
                                    f"Automatische Abschluss-Mail an {cust['email']} gesendet.", "email_sent"))
                    except Exception as e:
                        print(f"[TICKET] Abschluss-Mail Fehler: {e}")

        db.execute("UPDATE tickets SET status=%s, updated_at=CURRENT_TIMESTAMP WHERE id=%s", (new_status, tid))

    if body:
        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type, time_minutes)
                      VALUES (%s,%s,%s,%s,%s,%s)""",
                   (tid, session["user_id"], session["username"], body, update_type, time_minutes))
        db.execute("UPDATE tickets SET is_read=0, updated_at=CURRENT_TIMESTAMP WHERE id=%s", (tid,))

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
                            WHERE t.id=%s""", (tid,)).fetchone()
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
                      VALUES (%s,%s,%s,%s,%s)""",
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
        db.execute("INSERT INTO outreach (customer_id, subject, body) VALUES (%s,%s,%s)", (cid, subject, body))
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
        "SELECT * FROM articles WHERE (name LIKE %s OR description LIKE %s) AND active=1 LIMIT 8",
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
                      VALUES (%s,%s,%s,%s,%s,%s,%s,%s)""",
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
    article = db.execute("SELECT * FROM articles WHERE id=%s", (aid,)).fetchone()
    if request.method == "POST":
        db.execute("""UPDATE articles SET article_number=%s,name=%s,description=%s,category=%s,unit=%s,
                      unit_price=%s,tax_rate=%s,active=%s WHERE id=%s""",
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
    db.execute("DELETE FROM articles WHERE id=%s", (aid,))
    db.commit()
    db.close()
    flash("Leistung gelöscht", "success")
    return redirect(url_for("articles"))


# ── Dokumente ─────────────────────────────────────────────────────────────────

def _doc_breadcrumb(db, folder_id):
    crumbs = []
    fid = folder_id
    while fid:
        row = db.execute("SELECT id, name, parent_id FROM documents WHERE id=%s AND type='folder'", (fid,)).fetchone()
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
        folder = db.execute("SELECT * FROM documents WHERE id=%s AND type='folder'", (folder_id,)).fetchone()
        if not folder:
            db.close()
            return redirect(url_for("documents"))
    else:
        folder = None
    if folder_id:
        items = db.execute(
            "SELECT * FROM documents WHERE parent_id = %s ORDER BY type DESC, name ASC",
            (folder_id,)
        ).fetchall()
    else:
        items = db.execute(
            "SELECT * FROM documents WHERE parent_id IS NULL ORDER BY type DESC, name ASC"
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
        db.execute("INSERT INTO documents (name, parent_id, type, uploaded_by) VALUES (%s,%s,%s,%s)",
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
        new_id = db.execute("""INSERT INTO documents (name, parent_id, type, file_path, file_size, mime_type, uploaded_by)
                      VALUES (%s,%s,%s,%s,%s,%s,%s) RETURNING id""",
                   (f.filename, parent_id, "file", safe, size, mime or "application/octet-stream", session["username"])).fetchone()["id"]
        log_activity(db, "hochgeladen", "Dokument", new_id, f.filename)
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
    doc = db.execute("SELECT * FROM documents WHERE id=%s AND type='file'", (did,)).fetchone()
    db.close()
    if not doc:
        flash("Datei nicht gefunden", "error")
        return redirect(url_for("documents"))
    safe_fp = os.path.basename(doc["file_path"])
    if not safe_fp:
        abort(400)
    return send_from_directory(DOC_STORE, safe_fp, as_attachment=True,
                               download_name=secure_filename(doc["name"] or safe_fp))


@app.route("/documents/<int:did>/view")
@login_required
def document_view(did):
    db = get_db()
    doc = db.execute("SELECT * FROM documents WHERE id=%s AND type='file'", (did,)).fetchone()
    db.close()
    if not doc:
        abort(404)
    safe_fp = os.path.basename(doc["file_path"])
    if not safe_fp:
        abort(400)
    return send_from_directory(DOC_STORE, safe_fp, as_attachment=False,
                               mimetype=doc["mime_type"] or "application/octet-stream")


@app.route("/documents/<int:did>/rename", methods=["POST"])
@login_required
def document_rename(did):
    new_name  = request.form.get("name", "").strip()
    parent_id = request.form.get("parent_id") or None
    if new_name:
        db = get_db()
        old = db.execute("SELECT name FROM documents WHERE id=%s", (did,)).fetchone()
        db.execute("UPDATE documents SET name=%s WHERE id=%s", (new_name, did))
        log_activity(db, "umbenannt", "Dokument", did, new_name,
                     f"vorher: {old['name']}" if old else None)
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
    doc = db.execute("SELECT * FROM documents WHERE id=%s", (did,)).fetchone()
    if doc and doc["type"] == "file" and doc["file_path"]:
        fp = os.path.join(DOC_STORE, doc["file_path"])
        if os.path.exists(fp):
            os.remove(fp)
    db.execute("DELETE FROM documents WHERE id=%s", (did,))
    if doc:
        log_activity(db, "gelöscht", "Dokument" if doc["type"] == "file" else "Ordner", did, doc["name"])
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


NOTIF_PREF_KEYS = [
    "notif_mention", "notif_new_ticket", "notif_new_invoice",
    "notif_invoice_paid", "notif_new_promoter", "notif_payout", "notif_sound",
]
NOTIF_TYPE_TO_PREF = {
    "mention": "notif_mention",
    "new_ticket": "notif_new_ticket",
    "new_invoice": "notif_new_invoice",
    "invoice_paid": "notif_invoice_paid",
    "promoter_register": "notif_new_promoter",
    "payout_request": "notif_payout",
}


def get_user_notif_prefs(uid, db):
    rows = db.execute(
        "SELECT pref_key, pref_value FROM user_notification_prefs WHERE user_id=%s", (uid,)
    ).fetchall()
    prefs = {r["pref_key"]: r["pref_value"] for r in rows}
    # Default all to enabled
    return {k: prefs.get(k, "1") for k in NOTIF_PREF_KEYS}


@app.route("/api/notifications")
@login_required
def api_notifications():
    uid = session["user_id"]
    is_admin = session.get("role") == "admin"
    db = get_db()
    prefs = get_user_notif_prefs(uid, db)
    if is_admin:
        rows = db.execute(
            """SELECT id, type, title, body, link FROM notifications
               WHERE is_read=0 AND (target_user_id=%s OR target_user_id IS NULL)
               ORDER BY created_at DESC LIMIT 20""", (uid,)
        ).fetchall()
    else:
        rows = db.execute(
            """SELECT id, type, title, body, link FROM notifications
               WHERE is_read=0 AND target_user_id=%s
               ORDER BY created_at DESC LIMIT 20""", (uid,)
        ).fetchall()
    db.close()
    # Filter by user prefs
    result = []
    for r in rows:
        pref_key = NOTIF_TYPE_TO_PREF.get(r["type"])
        if pref_key is None or prefs.get(pref_key, "1") == "1":
            d = dict(r)
            d["sound"] = prefs.get("notif_sound", "1")
            result.append(d)
    return jsonify(result[:10])


@app.route("/api/notifications/<int:nid>/read", methods=["POST"])
@login_required
def api_notification_read(nid):
    uid = session["user_id"]
    db = get_db()
    db.execute("UPDATE notifications SET is_read=1 WHERE id=%s AND (target_user_id=%s OR target_user_id IS NULL)", (nid, uid))
    db.commit()
    db.close()
    return jsonify(ok=True)


@app.route("/api/users")
@login_required
def api_users():
    db = get_db()
    rows = db.execute("SELECT username, display_name FROM users ORDER BY display_name").fetchall()
    db.close()
    return jsonify([dict(r) for r in rows])


@app.route("/api/search")
@login_required
def api_search():
    q = request.args.get("q", "").strip()
    if len(q) < 2:
        return jsonify(customers=[], invoices=[], tickets=[], documents=[])

    like = f"%{q}%"
    db = get_db()

    customers = db.execute("""
        SELECT id, name, company, email FROM customers
        WHERE name ILIKE %s OR company ILIKE %s OR email ILIKE %s
        ORDER BY name LIMIT 6
    """, (like, like, like)).fetchall()

    invoices = db.execute("""
        SELECT i.id, i.number, i.status, c.name as customer_name, c.company as customer_company
        FROM invoices i JOIN customers c ON c.id = i.customer_id
        WHERE i.number ILIKE %s OR c.name ILIKE %s OR c.company ILIKE %s
        ORDER BY i.created_at DESC LIMIT 6
    """, (like, like, like)).fetchall()

    tickets = db.execute("""
        SELECT t.id, t.title, t.status, c.name as customer_name, c.company as customer_company
        FROM tickets t LEFT JOIN customers c ON c.id = t.customer_id
        WHERE t.title ILIKE %s OR t.description ILIKE %s
        ORDER BY t.created_at DESC LIMIT 6
    """, (like, like)).fetchall()

    documents = db.execute("""
        SELECT id, name, parent_id FROM documents
        WHERE type='file' AND name ILIKE %s
        ORDER BY created_at DESC LIMIT 6
    """, (like,)).fetchall()

    db.close()
    return jsonify(
        customers=[dict(r) for r in customers],
        invoices=[dict(r) for r in invoices],
        tickets=[dict(r) for r in tickets],
        documents=[dict(r) for r in documents],
    )


# ── Backup ────────────────────────────────────────────────────────────────────

def _safe_path_component(name):
    name = (name or "").strip().replace("/", "-").replace("\\", "-")
    return name or "Unbenannt"


def _build_document_arcnames(db):
    """Map each file-type document id to a human-readable zip path that mirrors
    the folder structure and original filenames shown in the Dokumente module."""
    rows = db.execute("SELECT id, name, parent_id, type, file_path FROM documents").fetchall()
    by_id = {r["id"]: r for r in rows}

    def folder_path(folder_id):
        parts = []
        seen = set()
        while folder_id is not None and folder_id in by_id and folder_id not in seen:
            seen.add(folder_id)
            node = by_id[folder_id]
            parts.append(_safe_path_component(node["name"]))
            folder_id = node["parent_id"]
        return list(reversed(parts))

    arcnames = {}
    used_names = {}
    for r in rows:
        if r["type"] != "file":
            continue
        folder_parts = folder_path(r["parent_id"])
        base_name = _safe_path_component(r["name"] or os.path.basename(r["file_path"] or ""))
        dir_key = tuple(folder_parts)
        used_names.setdefault(dir_key, set())
        final_name = base_name
        n = 1
        while final_name in used_names[dir_key]:
            stem, ext = os.path.splitext(base_name)
            final_name = f"{stem} ({n}){ext}"
            n += 1
        used_names[dir_key].add(final_name)
        arcnames[r["id"]] = "/".join(["Dokumente"] + folder_parts + [final_name])
    return arcnames


@app.route("/backup")
@admin_required
def backup():
    import zipfile, io, subprocess
    data_dir = os.path.join(os.path.dirname(__file__), "data")
    doc_store_dir = os.path.join(data_dir, "documents")
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")

    db = get_db()
    doc_arcnames = _build_document_arcnames(db)
    doc_rows = {r["id"]: r for r in db.execute("SELECT id, file_path FROM documents WHERE type='file'").fetchall()}
    db.close()

    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        # Live database dump (Postgres) — this is the actual business data
        # and previously was NOT part of the backup at all.
        pg_env = dict(os.environ, PGPASSWORD=os.environ.get("DB_PASSWORD", ""))
        try:
            dump = subprocess.run(
                ["pg_dump", "-h", os.environ.get("DB_HOST", "db"),
                 "-p", os.environ.get("DB_PORT", "5432"),
                 "-U", os.environ.get("DB_USER", "itool"),
                 "-d", os.environ.get("DB_NAME", "itool"),
                 "--no-owner", "--no-privileges"],
                env=pg_env, capture_output=True, timeout=120, check=True,
            )
            zf.writestr(f"datenbank/itool_{ts}.sql", dump.stdout)
        except Exception as e:
            zf.writestr("datenbank/FEHLER.txt",
                        f"Datenbank-Dump fehlgeschlagen: {e}\n"
                        f"Die Dateien in diesem Backup sind trotzdem vollstaendig, "
                        f"aber OHNE Datenbankinhalte (Kunden, Rechnungen, Tickets ...).")

        # Dokumente: reconstructed folder structure with original filenames
        for doc_id, arcname in doc_arcnames.items():
            row = doc_rows.get(doc_id)
            if not row or not row["file_path"]:
                continue
            full = os.path.join(doc_store_dir, os.path.basename(row["file_path"]))
            if os.path.exists(full):
                zf.write(full, arcname)

        # Everything else (uploads, accounting imports, ...) unchanged
        for root, dirs, files in os.walk(data_dir):
            if os.path.commonpath([root, doc_store_dir]) == doc_store_dir:
                continue  # already handled above with proper names/paths
            for fname in files:
                if fname.endswith(".db"):
                    continue  # veraltete sqlite-Reste, falls noch vorhanden
                full = os.path.join(root, fname)
                arcname = os.path.relpath(full, os.path.dirname(data_dir))
                zf.write(full, arcname)
    buf.seek(0)
    return send_file(
        buf,
        as_attachment=True,
        download_name=f"systemhaus24_backup_{ts}.zip",
        mimetype="application/zip",
    )


# ── Profile ───────────────────────────────────────────────────────────────────

@app.route("/profile")
@login_required
def profile():
    db = get_db()
    user = db.execute("SELECT * FROM users WHERE id=%s", (session["user_id"],)).fetchone()
    db.close()
    return render_template("profile.html", user=user)


@app.route("/favicon.ico")
@app.route("/favicon.png")
@app.route("/favicon.svg")
def favicon():
    return send_from_directory("static", "favicon.svg", mimetype="image/svg+xml")


# ── Aktivitätsprotokoll ────────────────────────────────────────────────────────

@app.route("/activity")
@admin_required
def activity_log():
    db = get_db()

    entity_type = request.args.get("entity_type", "")
    username    = request.args.get("username", "")
    page        = max(int(request.args.get("page", 1) or 1), 1)
    per_page    = 50

    where = []
    params = []
    if entity_type:
        where.append("entity_type = %s")
        params.append(entity_type)
    if username:
        where.append("username = %s")
        params.append(username)
    where_sql = ("WHERE " + " AND ".join(where)) if where else ""

    total = db.execute(f"SELECT COUNT(*) FROM audit_log {where_sql}", params).fetchone()[0]
    rows = db.execute(
        f"SELECT * FROM audit_log {where_sql} ORDER BY created_at DESC LIMIT %s OFFSET %s",
        params + [per_page, (page - 1) * per_page]
    ).fetchall()

    entity_types = [r[0] for r in db.execute(
        "SELECT DISTINCT entity_type FROM audit_log ORDER BY entity_type").fetchall()]
    usernames = [r[0] for r in db.execute(
        "SELECT DISTINCT username FROM audit_log ORDER BY username").fetchall()]

    db.close()
    return render_template("activity_log.html", rows=rows, entity_types=entity_types,
                           usernames=usernames, entity_type=entity_type, username=username,
                           page=page, total=total, per_page=per_page)


# ── User Management ───────────────────────────────────────────────────────────

@app.route("/users")
@admin_required
def users_list():
    db = get_db()
    users = db.execute("SELECT id, username, display_name, role FROM users ORDER BY role, username").fetchall()
    db.close()
    return render_template("users.html", users=users)


@app.route("/users/add", methods=["POST"])
@admin_required
def users_add():
    username    = request.form.get("username", "").strip()
    display     = request.form.get("display_name", "").strip()
    password    = request.form.get("password", "")
    role        = request.form.get("role", "user")
    if role not in ("admin", "user"):
        role = "user"
    if not username or not password:
        flash("Benutzername und Passwort erforderlich.", "error")
        return redirect(url_for("users_list"))
    db = get_db()
    if db.execute("SELECT id FROM users WHERE username=%s", (username,)).fetchone():
        db.close()
        flash(f"Benutzername '{username}' ist bereits vergeben.", "error")
        return redirect(url_for("users_list"))
    db.execute(
        "INSERT INTO users (username, password_hash, display_name, role) VALUES (%s,%s,%s,%s)",
        (username, generate_password_hash(password), display or username, role),
    )
    db.commit()
    db.close()
    flash(f"Benutzer '{username}' angelegt.", "success")
    return redirect(url_for("users_list"))


@app.route("/users/<int:uid>/role", methods=["POST"])
@admin_required
def users_set_role(uid):
    if uid == session["user_id"]:
        flash("Du kannst deine eigene Rolle nicht ändern.", "error")
        return redirect(url_for("users_list"))
    role = request.form.get("role", "user")
    if role not in ("admin", "user"):
        role = "user"
    db = get_db()
    db.execute("UPDATE users SET role=%s WHERE id=%s AND role != 'promoter'", (role, uid))
    db.commit()
    db.close()
    flash("Rolle aktualisiert.", "success")
    return redirect(url_for("users_list"))


@app.route("/users/<int:uid>/delete", methods=["POST"])
@admin_required
def users_delete(uid):
    if uid == session["user_id"]:
        flash("Du kannst dich nicht selbst löschen.", "error")
        return redirect(url_for("users_list"))
    db = get_db()
    db.execute("DELETE FROM users WHERE id=%s AND role != 'promoter'", (uid,))
    db.commit()
    db.close()
    flash("Benutzer gelöscht.", "success")
    return redirect(url_for("users_list"))


@app.route("/users/<int:uid>/reset-password", methods=["POST"])
@admin_required
def users_reset_password(uid):
    new_pw = request.form.get("password", "")
    if not new_pw:
        flash("Passwort darf nicht leer sein.", "error")
        return redirect(url_for("users_list"))
    db = get_db()
    db.execute("UPDATE users SET password_hash=%s WHERE id=%s", (generate_password_hash(new_pw), uid))
    db.commit()
    db.close()
    flash("Passwort zurückgesetzt.", "success")
    return redirect(url_for("users_list"))


# ── Settings ──────────────────────────────────────────────────────────────────

SETTING_KEYS_BY_TAB = {
    "firma": [
        "company_name", "company_street", "company_zip", "company_city",
        "company_phone", "company_email", "company_website", "company_tax_id",
        "company_iban", "company_bic", "company_bank", "company_kleingewerbe",
    ],
    "layout": [
        "accent_color", "chat_position",
    ],
    "smtp": [
        "smtp_host", "smtp_port", "smtp_user", "smtp_pass",
        "smtp_from_name", "smtp_from_email", "error_notify_email",
    ],
    "imap": [
        "imap_host", "imap_port", "imap_user", "imap_pass",
        "imap_enabled", "imap_folder", "imap_auto_ticket",
    ],
}


def _shade_hex(hex_color, factor=0.82):
    """Shade a #rrggbb color: factor<1 darkens, factor>1 lightens toward white."""
    try:
        h = hex_color.lstrip("#")
        r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
        if factor <= 1:
            r, g, b = r * factor, g * factor, b * factor
        else:
            t = factor - 1
            r, g, b = r + (255 - r) * t, g + (255 - g) * t, b + (255 - b) * t
        r, g, b = (max(0, min(255, int(v))) for v in (r, g, b))
        return f"#{r:02x}{g:02x}{b:02x}"
    except Exception:
        return hex_color


def _darken_hex(hex_color, factor=0.82):
    return _shade_hex(hex_color, factor)


app.jinja_env.globals["darken_hex"] = _darken_hex
app.jinja_env.globals["shade_hex"] = _shade_hex


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
    uid = session["user_id"]
    notif_prefs = get_user_notif_prefs(uid, db)
    db.close()
    return render_template("settings.html", cfg=cfg, notif_prefs=notif_prefs)


@app.route("/settings/notifications", methods=["POST"])
@login_required
def settings_notifications():
    db = get_db()
    uid = session["user_id"]
    for key in NOTIF_PREF_KEYS:
        val = "1" if request.form.get(key) else "0"
        db.execute(
            """INSERT INTO user_notification_prefs (user_id, pref_key, pref_value)
               VALUES (%s, %s, %s)
               ON CONFLICT (user_id, pref_key) DO UPDATE SET pref_value=%s""",
            (uid, key, val, val)
        )
    db.commit()
    db.close()
    flash("Benachrichtigungseinstellungen gespeichert", "success")
    return redirect(url_for("settings") + "#benachrichtigungen")


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
    row = db.execute("SELECT avatar FROM users WHERE id=%s", (uid,)).fetchone()
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
        db.execute("UPDATE users SET avatar=%s WHERE id=%s", (filename, uid))
        db.commit()
        db.close()
        flash("Avatar gespeichert", "success")
    dest = url_for("settings") + "#allgemein" if session.get("role") == "admin" else url_for("profile")
    return redirect(dest)


@app.route("/settings/display-name", methods=["POST"])
@login_required
def settings_display_name():
    name = request.form.get("display_name", "").strip()
    if name:
        db = get_db()
        db.execute("UPDATE users SET display_name=%s WHERE id=%s", (name, session["user_id"]))
        db.commit()
        db.close()
        session["display_name"] = name
        flash("Anzeigename gespeichert", "success")
    dest = url_for("settings") + "#allgemein" if session.get("role") == "admin" else url_for("profile")
    return redirect(dest)


@app.route("/settings/change-password", methods=["POST"])
@login_required
def settings_change_password():
    current  = request.form.get("current_password", "")
    new_pw   = request.form.get("new_password", "")
    confirm  = request.form.get("confirm_password", "")
    db = get_db()
    user = db.execute("SELECT * FROM users WHERE id=%s", (session["user_id"],)).fetchone()
    if not check_password_hash(user["password_hash"], current):
        flash("Aktuelles Passwort ist falsch", "error")
    elif len(new_pw) < 6:
        flash("Neues Passwort muss mindestens 6 Zeichen haben", "error")
    elif new_pw != confirm:
        flash("Passwörter stimmen nicht überein", "error")
    else:
        db.execute("UPDATE users SET password_hash=%s WHERE id=%s",
                   (generate_password_hash(new_pw), session["user_id"]))
        db.commit()
        flash("Passwort erfolgreich geändert", "success")
    db.close()
    dest = url_for("settings") + "#allgemein" if session.get("role") == "admin" else url_for("profile")
    return redirect(dest)


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
                    "SELECT id FROM customers WHERE LOWER(email)=%s OR LOWER(contact_email)=%s LIMIT 1",
                    (from_email, from_email)).fetchone()
                customer_id = cust["id"] if cust else None

                # check if this is a reply to an existing ticket via [#ID] in subject
                import re as _re
                tid_match = _re.search(r'\[#(\d+)\]', subject)
                if tid_match:
                    existing_tid = int(tid_match.group(1))
                    exists = db.execute("SELECT id FROM tickets WHERE id=%s", (existing_tid,)).fetchone()
                    if exists:
                        db.execute("""INSERT INTO ticket_updates (ticket_id, user_id, username, body, update_type)
                                      VALUES (%s,%s,%s,%s,%s)""",
                                   (existing_tid, None, from_hdr, body or "(kein Text)", "email_reply"))
                        db.execute("UPDATE tickets SET is_read=0, updated_at=CURRENT_TIMESTAMP WHERE id=%s",
                                   (existing_tid,))
                        print(f"[IMAP] Antwort zu Ticket #{existing_tid} hinzugefügt")
                        M.store(uid, "+FLAGS", "\\Seen")
                        count += 1
                        continue

                # no match → new ticket
                db.execute(
                    "INSERT INTO tickets (title, description, priority, status, customer_id, is_read) VALUES (%s,%s,%s,%s,%s,0)",
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
        "SELECT * FROM promoter_tokens WHERE token=%s AND used_by IS NULL", (token,)).fetchone()
    if not tok:
        db.close()
        return render_template("promoter_register.html", error="Ungültiger oder bereits verwendeter Link.")
    # Token expires after 72 hours
    created = tok["created_at"] if isinstance(tok["created_at"], datetime) else datetime.strptime(str(tok["created_at"])[:19], "%Y-%m-%d %H:%M:%S")
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
        if db.execute("SELECT id FROM users WHERE username=%s", (username,)).fetchone():
            return render_template("promoter_register.html", error="Benutzername bereits vergeben.")
        phash = generate_password_hash(pw)
        new_uid = db.execute(
            "INSERT INTO users (username, password_hash, display_name, role) VALUES (%s,%s,%s,%s) RETURNING id",
            (username, phash, display or username, "promoter")).fetchone()["id"]
        db.execute("UPDATE promoter_tokens SET used_by=%s, used_at=CURRENT_TIMESTAMP WHERE id=%s",
                   (new_uid, tok["id"]))
        db.execute(
            "INSERT INTO notifications (type, title, body, link) VALUES (%s,%s,%s,%s)",
            ("promoter_register", "Neuer Promoter registriert",
             f"{display or username} hat sich als Promoter registriert.",
             f"/promoters/{new_uid}"))
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
    db.execute("INSERT INTO promoter_tokens (token, created_by) VALUES (%s,%s)",
               (token, session["user_id"]))
    db.commit()
    db.close()
    flash(f"Registrierungslink erstellt: {request.host_url}register/{token}", "success")
    return redirect(url_for("promoters"))


@app.route("/promoters/<int:pid>")
@admin_required
def promoter_detail(pid):
    db = get_db()
    promoter = db.execute("SELECT * FROM users WHERE id=%s AND role='promoter'", (pid,)).fetchone()
    if not promoter:
        db.close()
        flash("Promoter nicht gefunden.", "error")
        return redirect(url_for("promoters"))
    assignments = db.execute("""
        SELECT pa.*, c.name as customer_name, c.company as customer_company
        FROM promoter_assignments pa
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=%s
        ORDER BY pa.created_at DESC
    """, (pid,)).fetchall()
    commissions = db.execute("""
        SELECT pc.*, i.number as invoice_number, i.date as invoice_date,
               c.name as customer_name
        FROM promoter_commissions pc
        JOIN promoter_assignments pa ON pa.id = pc.assignment_id
        JOIN invoices i ON i.id = pc.invoice_id
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=%s
        ORDER BY pc.created_at DESC
    """, (pid,)).fetchall()
    payouts = db.execute("""
        SELECT pp.*, u.username as decided_by_name
        FROM promoter_payouts pp
        LEFT JOIN users u ON u.id = pp.decided_by
        WHERE pp.promoter_id=%s
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
        VALUES (%s,%s,%s,%s,%s,%s,%s)
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
    row = db.execute("SELECT promoter_id FROM promoter_assignments WHERE id=%s", (aid,)).fetchone()
    db.execute("DELETE FROM promoter_assignments WHERE id=%s", (aid,))
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
    payout = db.execute("SELECT * FROM promoter_payouts WHERE id=%s", (poid,)).fetchone()
    if payout and decision in ("approved", "rejected"):
        db.execute("""
            UPDATE promoter_payouts
            SET status=%s, decided_at=CURRENT_TIMESTAMP, decided_by=%s, admin_notes=%s
            WHERE id=%s
        """, (decision, session["user_id"], notes, poid))
        if decision == "approved":
            # mark commissions as paid
            db.execute("""
                UPDATE promoter_commissions SET payout_id=%s
                WHERE payout_id IS NULL
                  AND assignment_id IN (
                    SELECT id FROM promoter_assignments WHERE promoter_id=%s
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
        WHERE pa.promoter_id=%s
        ORDER BY pc.created_at DESC
    """, (pid,)).fetchall()
    payouts = db.execute("""
        SELECT pp.*, u.username as decided_by_name
        FROM promoter_payouts pp
        LEFT JOIN users u ON u.id = pp.decided_by
        WHERE pp.promoter_id=%s
        ORDER BY pp.requested_at DESC
    """, (pid,)).fetchall()
    assignments = db.execute("""
        SELECT pa.*, c.name as customer_name, c.company as customer_company
        FROM promoter_assignments pa
        JOIN customers c ON c.id = pa.customer_id
        WHERE pa.promoter_id=%s
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
        WHERE pa.promoter_id=%s
    """, (pid,)).fetchone()["t"]
    paid_or_pending = db.execute("""
        SELECT COALESCE(SUM(amount),0) as t FROM promoter_payouts
        WHERE promoter_id=%s AND status IN ('approved','pending')
    """, (pid,)).fetchone()["t"]
    balance = round(earned - paid_or_pending, 2)
    if balance <= 0:
        flash("Kein auszahlbares Guthaben vorhanden.", "error")
        db.close()
        return redirect(url_for("promoter_dashboard"))
    db.execute("INSERT INTO promoter_payouts (promoter_id, amount) VALUES (%s,%s)", (pid, balance))
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
          AND DATE(tu.created_at) BETWEEN %s AND %s
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
        "revenue_month":    revenue("WHERE i.status IN ('sent','paid') AND TO_CHAR(i.date::date,'YYYY-MM')=%s",
                                    (now.strftime("%Y-%m"),)),
        "revenue_year":     revenue("WHERE i.status IN ('sent','paid') AND TO_CHAR(i.date::date,'YYYY')=%s",
                                    (now.strftime("%Y"),)),
        "revenue_total":    revenue("WHERE i.status IN ('sent','paid')"),
        "outstanding":      revenue("WHERE i.status='sent'"),
        "paid_month":       revenue("WHERE i.status='paid' AND TO_CHAR(i.date::date,'YYYY-MM')=%s",
                                    (now.strftime("%Y-%m"),)),
        "draft_total":      revenue("WHERE i.status='draft'"),
        "count_sent":       db.execute("SELECT COUNT(*) FROM invoices WHERE status='sent'").fetchone()[0],
        "count_paid_month": db.execute("SELECT COUNT(*) FROM invoices WHERE status='paid' AND TO_CHAR(date::date,'YYYY-MM')=%s",
                                       (now.strftime("%Y-%m"),)).fetchone()[0],
        "count_draft":      db.execute("SELECT COUNT(*) FROM invoices WHERE status='draft'").fetchone()[0],
    }

    # Monthly revenue for last 12 months
    monthly = db.execute("""
        SELECT TO_CHAR(i.date::date, 'YYYY-MM') as month,
               SUM(ii.quantity*ii.unit_price) as total,
               COUNT(DISTINCT i.id) as count
        FROM invoices i JOIN invoice_items ii ON ii.invoice_id=i.id
        WHERE i.status IN ('sent','paid')
          AND i.date::date >= CURRENT_DATE - INTERVAL '12 months'
        GROUP BY month ORDER BY month
    """).fetchall()

    # Unpaid invoices (sent but not paid) — oldest first
    unpaid = db.execute("""
        SELECT i.*, c.name as customer_name, c.company as customer_company,
               COALESCE((SELECT SUM(quantity*unit_price) FROM invoice_items WHERE invoice_id=i.id),0) as total,
               CASE WHEN i.due_date IS NOT NULL AND i.due_date != '' THEN (CURRENT_DATE - i.due_date::date) ELSE NULL END as overdue_days
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
        "INSERT INTO expenses (date, category, description, amount_netto, tax_rate, receipt_file, notes) VALUES (%s,%s,%s,%s,%s,%s,%s)",
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
    row = db.execute("SELECT receipt_file FROM expenses WHERE id=%s", (eid,)).fetchone()
    if row and row["receipt_file"]:
        path = os.path.join(RECEIPT_DIR, row["receipt_file"])
        if os.path.isfile(path):
            os.remove(path)
    db.execute("DELETE FROM expenses WHERE id=%s", (eid,))
    db.commit()
    db.close()
    flash("Ausgabe gelöscht.", "success")
    return redirect(url_for("accounting"))


@app.route("/accounting/expenses/<int:eid>/receipt")
@login_required
def expense_receipt(eid):
    db = get_db()
    row = db.execute("SELECT receipt_file FROM expenses WHERE id=%s", (eid,)).fetchone()
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
    inv_id = db.execute(
        "INSERT INTO invoices (number, customer_id, date, due_date, status, notes) VALUES (%s,%s,%s,%s,%s,%s) RETURNING id",
        (num, rec["customer_id"], rec["next_date"], due, "draft",
         f"Automatisch erstellt aus Vorlage: {rec['name']}")
    ).fetchone()["id"]
    items = db.execute("SELECT * FROM recurring_invoice_items WHERE recurring_id=%s", (rec["id"],)).fetchall()
    for it in items:
        db.execute("INSERT INTO invoice_items (invoice_id, description, quantity, unit_price) VALUES (%s,%s,%s,%s)",
                   (inv_id, it["description"], it["quantity"], it["unit_price"]))
    # Advance next_date
    new_next = _next_date(rec["next_date"], rec["interval"])
    db.execute("UPDATE recurring_invoices SET next_date=%s, last_created=%s WHERE id=%s",
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
                "SELECT * FROM recurring_invoices WHERE status='active' AND next_date<=%s", (today,)
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
    filter_customer_id = request.args.get("customer_id", "")
    query = """
        SELECT r.*, c.name as customer_name, c.company as customer_company,
               (SELECT COALESCE(SUM(quantity*unit_price),0) FROM recurring_invoice_items WHERE recurring_id=r.id) as total
        FROM recurring_invoices r
        JOIN customers c ON c.id=r.customer_id
    """
    params = []
    if filter_customer_id:
        query += " WHERE r.customer_id=%s"
        params.append(filter_customer_id)
    query += " ORDER BY r.status DESC, r.next_date ASC"
    recs = db.execute(query, params).fetchall()
    customers = db.execute("SELECT id, name, company FROM customers WHERE status='customer' ORDER BY name").fetchall()
    filter_customers = db.execute("""
        SELECT DISTINCT c.id, c.name, c.company FROM customers c
        JOIN recurring_invoices r ON r.customer_id=c.id ORDER BY c.name
    """).fetchall()
    db.close()
    interval_labels = {"monthly": "Monatlich", "quarterly": "Vierteljährlich", "yearly": "Jährlich"}
    return render_template("recurring.html", recs=recs, customers=customers,
                           filter_customers=filter_customers, filter_customer_id=filter_customer_id,
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
    rid = db.execute(
        "INSERT INTO recurring_invoices (customer_id, name, interval, day_of_month, next_date, notes) VALUES (%s,%s,%s,%s,%s,%s) RETURNING id",
        (customer_id, name, interval, int(start_date.split("-")[2]), start_date, notes)
    ).fetchone()["id"]
    for desc, qty, price in zip(descriptions, quantities, prices):
        desc = desc.strip()
        if not desc:
            continue
        try:
            qty   = float(qty or 1)
            price = float(price or 0)
        except ValueError:
            continue
        db.execute("INSERT INTO recurring_invoice_items (recurring_id, description, quantity, unit_price) VALUES (%s,%s,%s,%s)",
                   (rid, desc, qty, price))
    db.commit()
    db.close()
    flash("Wiederkehrende Rechnung erstellt.", "success")
    return redirect(url_for("recurring_list"))


@app.route("/recurring/<int:rid>/toggle", methods=["POST"])
@login_required
def recurring_toggle(rid):
    db = get_db()
    rec = db.execute("SELECT status FROM recurring_invoices WHERE id=%s", (rid,)).fetchone()
    if rec:
        new_status = "paused" if rec["status"] == "active" else "active"
        db.execute("UPDATE recurring_invoices SET status=%s WHERE id=%s", (new_status, rid))
        db.commit()
    db.close()
    return redirect(url_for("recurring_list"))


@app.route("/recurring/<int:rid>/run-now", methods=["POST"])
@login_required
def recurring_run_now(rid):
    db = get_db()
    rec = db.execute("SELECT * FROM recurring_invoices WHERE id=%s", (rid,)).fetchone()
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
    db.execute("DELETE FROM recurring_invoices WHERE id=%s", (rid,))
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
        VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
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
    lead = db.execute("SELECT * FROM leads WHERE id=%s", (lid,)).fetchone()
    if not lead:
        db.close()
        flash("Lead nicht gefunden.", "error")
        return redirect(url_for("akquise"))
    activities = db.execute(
        "SELECT * FROM lead_activities WHERE lead_id=%s ORDER BY created_at DESC", (lid,)
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
    db.execute("UPDATE leads SET stage=%s, lost_reason=%s, updated_at=CURRENT_TIMESTAMP WHERE id=%s",
               (new_stage, lost_reason if new_stage == "lost" else None, lid))
    # Auto-activity log
    labels = {s[0]: s[1] for s in LEAD_STAGES}
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (%s,%s,%s,%s)",
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
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (%s,%s,%s,%s)",
               (lid, atype, body, session["username"]))
    db.execute("UPDATE leads SET updated_at=CURRENT_TIMESTAMP, next_followup=%s WHERE id=%s",
               (followup, lid))
    db.commit()
    db.close()
    return redirect(url_for("akquise_detail", lid=lid))


@app.route("/akquise/<int:lid>/edit", methods=["POST"])
@login_required
def akquise_edit(lid):
    db = get_db()
    db.execute("""UPDATE leads SET company=%s, contact_name=%s, contact_email=%s,
                  contact_phone=%s, source=%s, deal_value=%s, notes=%s, next_followup=%s,
                  updated_at=CURRENT_TIMESTAMP WHERE id=%s""", (
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
    db.execute("DELETE FROM leads WHERE id=%s", (lid,))
    db.commit()
    db.close()
    flash("Lead gelöscht.", "success")
    return redirect(url_for("akquise"))


@app.route("/akquise/<int:lid>/convert", methods=["POST"])
@login_required
def akquise_convert(lid):
    """Convert a won lead into a customer."""
    db = get_db()
    lead = db.execute("SELECT * FROM leads WHERE id=%s", (lid,)).fetchone()
    if not lead:
        db.close()
        flash("Lead nicht gefunden.", "error")
        return redirect(url_for("akquise"))
    cnum = next_customer_number(db)
    db.execute("""INSERT INTO customers (customer_number, name, company, email, phone, source, status)
                  VALUES (%s,%s,%s,%s,%s,%s,%s)""", (
        cnum,
        lead["contact_name"],
        lead["company"] or "",
        lead["contact_email"] or "",
        lead["contact_phone"] or "",
        lead["source"] or "",
        "customer",
    ))
    db.execute("UPDATE leads SET stage='won', updated_at=CURRENT_TIMESTAMP WHERE id=%s", (lid,))
    db.execute("INSERT INTO lead_activities (lead_id, type, body, created_by) VALUES (%s,%s,%s,%s)",
               (lid, "converted", f"In Kunde umgewandelt (Kundennr. {cnum})", session["username"]))
    db.commit()
    db.close()
    flash(f"Lead als Kunde angelegt ({cnum}).", "success")
    return redirect(url_for("akquise"))


# ── Init ──────────────────────────────────────────────────────────────────────

def _startup():
    init_db()
    db = get_db()
    existing = db.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    db.close()
    if existing == 0:
        print("Kein Benutzer vorhanden — Ersteinrichtung unter /setup erforderlich.")
    t = threading.Thread(target=imap_loop, daemon=True)
    t.start()
    t2 = threading.Thread(target=check_recurring_invoices, daemon=True)
    t2.start()
    print("[RECURRING] Hintergrund-Job gestartet (stündliche Prüfung)")

_startup()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000, debug=False)
