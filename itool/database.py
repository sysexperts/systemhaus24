import os
import psycopg2
import psycopg2.extras
import psycopg2.extensions


def _conn_params():
    return {
        "host":     os.environ.get("DB_HOST", "db"),
        "port":     int(os.environ.get("DB_PORT", 5432)),
        "dbname":   os.environ.get("DB_NAME", "itool"),
        "user":     os.environ.get("DB_USER", "itool"),
        "password": os.environ.get("DB_PASSWORD", ""),
    }


class _Row(dict):
    """Dict row that also supports numeric index access like sqlite3.Row."""
    def __getitem__(self, key):
        if isinstance(key, int):
            return list(self.values())[key]
        return super().__getitem__(key)


class _RowCursor(psycopg2.extras.RealDictCursor):
    """RealDictCursor that returns _Row instances."""
    def fetchone(self):
        row = super().fetchone()
        return _Row(row) if row is not None else None

    def fetchall(self):
        return [_Row(r) for r in super().fetchall()]


class _Cursor:
    """Thin cursor wrapper to behave like sqlite3 cursor."""
    def __init__(self, cur):
        self._cur = cur
        self.lastrowid = None

    def fetchone(self):
        return self._cur.fetchone()

    def fetchall(self):
        return self._cur.fetchall()

    @property
    def rowcount(self):
        return self._cur.rowcount

    def __iter__(self):
        return iter(self._cur.fetchall())

    def __getitem__(self, idx):
        return self._cur.fetchall()[idx]


class _Connection:
    """Thin connection wrapper to make psycopg2 behave like sqlite3."""
    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=None):
        cur = self._conn.cursor(cursor_factory=_RowCursor)
        cur.execute(sql, params or ())
        return _Cursor(cur)

    def executemany(self, sql, params_seq):
        cur = self._conn.cursor()
        for p in params_seq:
            cur.execute(sql, p)
        return _Cursor(cur)

    def commit(self):
        self._conn.commit()

    def rollback(self):
        self._conn.rollback()

    def close(self):
        self._conn.close()


def get_db():
    conn = psycopg2.connect(
        **_conn_params(),
        cursor_factory=_RowCursor,
    )
    conn.autocommit = False
    return _Connection(conn)


def _safe_alter(conn, sql):
    try:
        conn.execute(sql)
        conn.commit()
    except Exception:
        conn.rollback()


def init_db():
    conn = get_db()

    stmts = [
        """CREATE TABLE IF NOT EXISTS users (
            id SERIAL PRIMARY KEY,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            avatar TEXT,
            display_name TEXT,
            role TEXT DEFAULT 'admin'
        )""",
        """CREATE TABLE IF NOT EXISTS customers (
            id SERIAL PRIMARY KEY,
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
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS invoices (
            id SERIAL PRIMARY KEY,
            number TEXT UNIQUE NOT NULL,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            date TEXT NOT NULL,
            due_date TEXT,
            status TEXT DEFAULT 'draft',
            notes TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS invoice_items (
            id SERIAL PRIMARY KEY,
            invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
            description TEXT NOT NULL,
            quantity REAL DEFAULT 1,
            unit_price REAL NOT NULL
        )""",
        """CREATE TABLE IF NOT EXISTS tickets (
            id SERIAL PRIMARY KEY,
            title TEXT NOT NULL,
            description TEXT,
            customer_id INTEGER REFERENCES customers(id),
            priority TEXT DEFAULT 'medium',
            status TEXT DEFAULT 'open',
            is_read INTEGER DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS outreach (
            id SERIAL PRIMARY KEY,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            subject TEXT NOT NULL,
            body TEXT NOT NULL,
            sent_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS feed_messages (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL REFERENCES users(id),
            username TEXT NOT NULL,
            body TEXT NOT NULL,
            attachment TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS ticket_updates (
            id SERIAL PRIMARY KEY,
            ticket_id INTEGER NOT NULL REFERENCES tickets(id) ON DELETE CASCADE,
            user_id INTEGER REFERENCES users(id),
            username TEXT NOT NULL,
            body TEXT NOT NULL,
            update_type TEXT DEFAULT 'comment',
            time_minutes INTEGER DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY,
            value TEXT
        )""",
        """CREATE TABLE IF NOT EXISTS invoice_emails (
            id SERIAL PRIMARY KEY,
            invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
            to_addr TEXT NOT NULL,
            subject TEXT,
            sent_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            sent_by TEXT
        )""",
        """CREATE TABLE IF NOT EXISTS documents (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            parent_id INTEGER REFERENCES documents(id) ON DELETE CASCADE,
            type TEXT NOT NULL DEFAULT 'file',
            file_path TEXT,
            file_size INTEGER DEFAULT 0,
            mime_type TEXT,
            uploaded_by TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS expenses (
            id SERIAL PRIMARY KEY,
            date TEXT NOT NULL,
            category TEXT NOT NULL DEFAULT 'Sonstiges',
            description TEXT NOT NULL,
            amount_netto REAL NOT NULL,
            tax_rate REAL DEFAULT 19,
            receipt_file TEXT,
            notes TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS recurring_invoices (
            id SERIAL PRIMARY KEY,
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            name TEXT NOT NULL,
            interval TEXT NOT NULL DEFAULT 'monthly',
            day_of_month INTEGER DEFAULT 1,
            next_date TEXT NOT NULL,
            status TEXT DEFAULT 'active',
            notes TEXT,
            last_created TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS recurring_invoice_items (
            id SERIAL PRIMARY KEY,
            recurring_id INTEGER NOT NULL REFERENCES recurring_invoices(id) ON DELETE CASCADE,
            description TEXT NOT NULL,
            quantity REAL DEFAULT 1,
            unit_price REAL NOT NULL
        )""",
        """CREATE TABLE IF NOT EXISTS leads (
            id SERIAL PRIMARY KEY,
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
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS lead_activities (
            id SERIAL PRIMARY KEY,
            lead_id INTEGER NOT NULL REFERENCES leads(id) ON DELETE CASCADE,
            type TEXT NOT NULL DEFAULT 'note',
            body TEXT NOT NULL,
            created_by TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS articles (
            id SERIAL PRIMARY KEY,
            article_number TEXT,
            name TEXT NOT NULL,
            description TEXT,
            category TEXT DEFAULT 'Dienstleistung',
            unit TEXT DEFAULT 'Stunde',
            unit_price REAL NOT NULL DEFAULT 0,
            tax_rate REAL DEFAULT 19,
            active INTEGER DEFAULT 1,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS promoter_tokens (
            id SERIAL PRIMARY KEY,
            token TEXT UNIQUE NOT NULL,
            created_by INTEGER REFERENCES users(id),
            used_by INTEGER REFERENCES users(id),
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            used_at TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS promoter_assignments (
            id SERIAL PRIMARY KEY,
            promoter_id INTEGER NOT NULL REFERENCES users(id),
            customer_id INTEGER NOT NULL REFERENCES customers(id),
            commission_pct REAL DEFAULT 25,
            start_date TEXT NOT NULL,
            end_date TEXT,
            notes TEXT,
            created_by INTEGER REFERENCES users(id),
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS promoter_payouts (
            id SERIAL PRIMARY KEY,
            promoter_id INTEGER NOT NULL REFERENCES users(id),
            amount REAL NOT NULL,
            status TEXT DEFAULT 'pending',
            requested_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            decided_at TIMESTAMP,
            decided_by INTEGER REFERENCES users(id),
            admin_notes TEXT
        )""",
        """CREATE TABLE IF NOT EXISTS promoter_commissions (
            id SERIAL PRIMARY KEY,
            assignment_id INTEGER NOT NULL REFERENCES promoter_assignments(id),
            invoice_id INTEGER NOT NULL REFERENCES invoices(id),
            invoice_total REAL NOT NULL,
            commission_pct REAL NOT NULL,
            amount REAL NOT NULL,
            payout_id INTEGER REFERENCES promoter_payouts(id),
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
        """CREATE TABLE IF NOT EXISTS customer_contacts (
            id SERIAL PRIMARY KEY,
            customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
            name TEXT NOT NULL,
            position TEXT,
            email TEXT,
            phone TEXT,
            mobile TEXT,
            notes TEXT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )""",
    ]

    for sql in stmts:
        conn.execute(sql)

    conn.commit()
    conn.close()


def next_customer_number(conn):
    row = conn.execute(
        "SELECT customer_number FROM customers WHERE customer_number IS NOT NULL ORDER BY id DESC LIMIT 1"
    ).fetchone()
    if not row or not row["customer_number"]:
        return "KD-0001"
    try:
        num = int(row["customer_number"].split("-")[1]) + 1
        return f"KD-{num:04d}"
    except Exception:
        return "KD-0001"
