import os, sys, shutil, re
import psycopg2

conn = psycopg2.connect(
    host=os.environ.get('DB_HOST', 'db'),
    port=os.environ.get('DB_PORT', '5432'),
    dbname=os.environ.get('DB_NAME', 'itool'),
    user=os.environ.get('DB_USER', 'itool'),
    password=os.environ.get('DB_PASSWORD', ''),
)
cur = conn.cursor()
cur.execute('SELECT id, parent_id, type, name, file_path FROM documents ORDER BY id')
rows = cur.fetchall()
by_id = {r[0]: r for r in rows}

def safe(name):
    return re.sub(r'[\/:*?"<>|]', '_', name).strip() or 'unbenannt'

def build_path(doc_id):
    parts = []
    cur_id = doc_id
    seen = set()
    while cur_id is not None:
        if cur_id in seen:
            break
        seen.add(cur_id)
        row = by_id.get(cur_id)
        if not row:
            break
        parts.append(safe(row[3]))
        cur_id = row[1]
    return list(reversed(parts))

OUT_DIR = sys.argv[1]
SRC_DIR = '/app/data/documents'

count = 0
for r in rows:
    doc_id, parent_id, dtype, name, file_path = r
    if dtype != 'file' or not file_path:
        continue
    folder_parts = build_path(parent_id) if parent_id else []
    dest_dir = os.path.join(OUT_DIR, *folder_parts) if folder_parts else OUT_DIR
    os.makedirs(dest_dir, exist_ok=True)
    src = os.path.join(SRC_DIR, file_path)
    dest = os.path.join(dest_dir, safe(name))
    # Namenskollisionen vermeiden
    base, ext = os.path.splitext(dest)
    i = 2
    while os.path.exists(dest):
        dest = f'{base} ({i}){ext}'
        i += 1
    if os.path.exists(src):
        shutil.copy2(src, dest)
        count += 1
    else:
        print(f'WARNUNG: Quelldatei fehlt: {src}', file=sys.stderr)

print(f'{count} Dokumente exportiert nach {OUT_DIR}')
