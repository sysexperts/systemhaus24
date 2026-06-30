import sqlite3
import os

DB_PATH = os.path.join(os.path.dirname(__file__), "data", "itool.db")


def get_db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def _safe_alter(conn, sql):
    try:
        conn.execute(sql)
    except Exception:
        pass


def init_db():
    conn = get_db()
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS customers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_number TEXT,
            company TEXT,
            legal_form TEXT,
            name TEXT NOT NULL,
            email TEXT,
            phone TEXT,
            website TEXT,
            street TEXT,
            zip TEXT,
            city TEXT,
            country TEXT DEFAULT 'Deutschland',
            tax_id TEXT,
            payment_terms TEXT DEFAULT '14 Tage netto',
            contact_person TEXT,
            contact_position TEXT,
            contact_email TEXT,
            contact_phone TEXT,
            contact_mobile TEXT,
            contract_type TEXT,
            support_level TEXT,
            contract_start TEXT,
            contract_end TEXT,
            monthly_rate REAL,
            num_workstations INTEGER,
            num_servers INTEGER,
            it_notes TEXT,
            source TEXT,
            notes TEXT,
            status TEXT DEFAULT 'lead',
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS invoices (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            number TEXT UNIQUE NOT NULL,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            date TEXT NOT NULL,
            due_date TEXT,
            status TEXT DEFAULT 'draft',
            notes TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS invoice_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
            description TEXT NOT NULL,
            quantity REAL DEFAULT 1,
            unit_price REAL NOT NULL
        );

        CREATE TABLE IF NOT EXISTS tickets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            title TEXT NOT NULL,
            description TEXT,
            customer_id INTEGER REFERENCES customers(id),
            priority TEXT DEFAULT 'medium',
            status TEXT DEFAULT 'open',
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS outreach (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            subject TEXT NOT NULL,
            body TEXT NOT NULL,
            sent_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS feed_messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL REFERENCES users(id),
            username TEXT NOT NULL,
            body TEXT NOT NULL,
            attachment TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS ticket_updates (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ticket_id INTEGER NOT NULL REFERENCES tickets(id) ON DELETE CASCADE,
            user_id INTEGER REFERENCES users(id),
            username TEXT NOT NULL,
            body TEXT NOT NULL,
            update_type TEXT DEFAULT 'comment',
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY,
            value TEXT
        );

        CREATE TABLE IF NOT EXISTS invoice_emails (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
            to_addr TEXT NOT NULL,
            subject TEXT,
            sent_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            sent_by TEXT
        );

        CREATE TABLE IF NOT EXISTS documents (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            parent_id INTEGER REFERENCES documents(id) ON DELETE CASCADE,
            type TEXT NOT NULL DEFAULT 'file',
            file_path TEXT,
            file_size INTEGER DEFAULT 0,
            mime_type TEXT,
            uploaded_by TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS expenses (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            date TEXT NOT NULL,
            category TEXT NOT NULL DEFAULT 'Sonstiges',
            description TEXT NOT NULL,
            amount_netto REAL NOT NULL,
            tax_rate REAL DEFAULT 19,
            receipt_file TEXT,
            notes TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS recurring_invoices (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            name TEXT NOT NULL,
            interval TEXT NOT NULL DEFAULT 'monthly',
            day_of_month INTEGER DEFAULT 1,
            next_date TEXT NOT NULL,
            status TEXT DEFAULT 'active',
            notes TEXT,
            last_created TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS recurring_invoice_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            recurring_id INTEGER NOT NULL REFERENCES recurring_invoices(id) ON DELETE CASCADE,
            description TEXT NOT NULL,
            quantity REAL DEFAULT 1,
            unit_price REAL NOT NULL
        );

        CREATE TABLE IF NOT EXISTS leads (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            company TEXT,
            contact_name TEXT NOT NULL,
            contact_email TEXT,
            contact_phone TEXT,
            source TEXT DEFAULT 'Sonstiges',
            stage TEXT DEFAULT 'new',
            deal_value REAL DEFAULT 0,
            notes TEXT,
            next_followup TEXT,
            lost_reason TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS lead_activities (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            lead_id INTEGER NOT NULL REFERENCES leads(id) ON DELETE CASCADE,
            type TEXT NOT NULL DEFAULT 'note',
            body TEXT NOT NULL,
            created_by TEXT,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS articles (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            article_number TEXT,
            name TEXT NOT NULL,
            description TEXT,
            category TEXT DEFAULT 'Dienstleistung',
            unit TEXT DEFAULT 'Stunde',
            unit_price REAL NOT NULL DEFAULT 0,
            tax_rate REAL DEFAULT 19,
            active INTEGER DEFAULT 1,
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );
    """)

    # Migrate existing customers table (add new columns if missing)
    new_cols = [
        "ALTER TABLE customers ADD COLUMN customer_number TEXT",
        "ALTER TABLE customers ADD COLUMN legal_form TEXT",
        "ALTER TABLE customers ADD COLUMN website TEXT",
        "ALTER TABLE customers ADD COLUMN street TEXT",
        "ALTER TABLE customers ADD COLUMN zip TEXT",
        "ALTER TABLE customers ADD COLUMN city TEXT",
        "ALTER TABLE customers ADD COLUMN country TEXT DEFAULT 'Deutschland'",
        "ALTER TABLE customers ADD COLUMN tax_id TEXT",
        "ALTER TABLE customers ADD COLUMN payment_terms TEXT DEFAULT '14 Tage netto'",
        "ALTER TABLE customers ADD COLUMN contact_person TEXT",
        "ALTER TABLE customers ADD COLUMN contact_position TEXT",
        "ALTER TABLE customers ADD COLUMN contact_email TEXT",
        "ALTER TABLE customers ADD COLUMN contact_phone TEXT",
        "ALTER TABLE customers ADD COLUMN contact_mobile TEXT",
        "ALTER TABLE customers ADD COLUMN contract_type TEXT",
        "ALTER TABLE customers ADD COLUMN support_level TEXT",
        "ALTER TABLE customers ADD COLUMN contract_start TEXT",
        "ALTER TABLE customers ADD COLUMN contract_end TEXT",
        "ALTER TABLE customers ADD COLUMN monthly_rate REAL",
        "ALTER TABLE customers ADD COLUMN num_workstations INTEGER",
        "ALTER TABLE customers ADD COLUMN num_servers INTEGER",
        "ALTER TABLE customers ADD COLUMN it_notes TEXT",
        "ALTER TABLE customers ADD COLUMN source TEXT",
    ]
    for sql in new_cols:
        _safe_alter(conn, sql)

    _safe_alter(conn, "ALTER TABLE tickets ADD COLUMN is_read INTEGER DEFAULT 0")
    _safe_alter(conn, "ALTER TABLE ticket_updates ADD COLUMN time_minutes INTEGER DEFAULT 0")
    conn.execute("UPDATE tickets SET is_read=1 WHERE is_read IS NULL")
    _safe_alter(conn, "ALTER TABLE feed_messages ADD COLUMN attachment TEXT")
    _safe_alter(conn, "ALTER TABLE users ADD COLUMN avatar TEXT")
    _safe_alter(conn, "ALTER TABLE users ADD COLUMN display_name TEXT")
    _safe_alter(conn, "ALTER TABLE users ADD COLUMN role TEXT DEFAULT 'admin'")
    conn.execute("UPDATE users SET role='admin' WHERE role IS NULL")

    conn.executescript("""
        CREATE TABLE IF NOT EXISTS promoter_tokens (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            token TEXT UNIQUE NOT NULL,
            created_by INTEGER REFERENCES users(id),
            used_by INTEGER REFERENCES users(id),
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            used_at DATETIME
        );

        CREATE TABLE IF NOT EXISTS promoter_assignments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            promoter_id INTEGER NOT NULL REFERENCES users(id),
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            commission_pct REAL DEFAULT 25,
            start_date TEXT NOT NULL,
            end_date TEXT,
            notes TEXT,
            created_by INTEGER REFERENCES users(id),
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS promoter_commissions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            assignment_id INTEGER NOT NULL REFERENCES promoter_assignments(id),
            invoice_id INTEGER NOT NULL REFERENCES invoices(id),
            invoice_total REAL NOT NULL,
            commission_pct REAL NOT NULL,
            amount REAL NOT NULL,
            payout_id INTEGER REFERENCES promoter_payouts(id),
            created_at DATETIME DEFAULT CURRENT_TIMESTAMP
        );

        CREATE TABLE IF NOT EXISTS promoter_payouts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            promoter_id INTEGER NOT NULL REFERENCES users(id),
            amount REAL NOT NULL,
            status TEXT DEFAULT 'pending',
            requested_at DATETIME DEFAULT CURRENT_TIMESTAMP,
            decided_at DATETIME,
            decided_by INTEGER REFERENCES users(id),
            admin_notes TEXT
        );
    """)

    conn.commit()
    conn.close()


def next_customer_number(conn):
    row = conn.execute("SELECT customer_number FROM customers WHERE customer_number IS NOT NULL ORDER BY id DESC LIMIT 1").fetchone()
    if not row or not row["customer_number"]:
        return "KD-0001"
    try:
        num = int(row["customer_number"].split("-")[1]) + 1
        return f"KD-{num:04d}"
    except Exception:
        return "KD-0001"
