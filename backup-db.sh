#!/bin/bash
set -euo pipefail

BASE_DIR=/opt/systemhaus24/backups
DATE_DIR=$(date +%Y-%m-%d)
TS=$(date +%Y%m%d_%H%M%S)
DAY_DIR="$BASE_DIR/$DATE_DIR"
mkdir -p "$DAY_DIR"

LOG_PREFIX="[$(date '+%Y-%m-%d %H:%M:%S')]"
echo "$LOG_PREFIX Starte Backup..."

# 1. Datenbank-Dump
DB_FILE="$DAY_DIR/db_${TS}.sql.gz"
docker exec itool-db-1 pg_dump -U itool itool | gzip > "$DB_FILE"
echo "$LOG_PREFIX DB-Dump erstellt: $DB_FILE ($(du -h "$DB_FILE" | cut -f1))"

# 2. Dokumente mit Originalnamen + Ordnerstruktur (wie im Tool sichtbar)
DOCS_EXPORT_REL="_backup_export_${TS}"
docker cp /opt/systemhaus24/export_documents.py itool-itool-1:/tmp/export_documents.py
docker exec itool-itool-1 python3 /tmp/export_documents.py "/app/data/${DOCS_EXPORT_REL}"
docker exec itool-itool-1 rm -f /tmp/export_documents.py
DOCS_FILE="$DAY_DIR/dokumente_${TS}.tar.gz"
tar -czf "$DOCS_FILE" -C "/opt/systemhaus24/itool/data/${DOCS_EXPORT_REL}" .
rm -rf "/opt/systemhaus24/itool/data/${DOCS_EXPORT_REL}"
echo "$LOG_PREFIX Dokumente (Originalstruktur) gesichert: $DOCS_FILE ($(du -h "$DOCS_FILE" | cut -f1))"

# 3. Komplettes Daten-Verzeichnis als Rohsicherung (inkl. Avatare, Belege, Buchhaltungsimporte etc.)
RAW_FILE="$DAY_DIR/data_roh_${TS}.tar.gz"
tar -czf "$RAW_FILE" -C /opt/systemhaus24/itool data
echo "$LOG_PREFIX Rohdaten gesichert: $RAW_FILE ($(du -h "$RAW_FILE" | cut -f1))"

# 4. Offsite-Upload zu Google Drive (gleiche Ordnerstruktur: itool-backups/YYYY-MM-DD/)
if command -v rclone >/dev/null 2>&1 && rclone listremotes 2>/dev/null | grep -q '^gdrive:'; then
  echo "$LOG_PREFIX Lade zu Google Drive hoch..."
  rclone copy "$DAY_DIR" "gdrive:itool-backups/$DATE_DIR/" --quiet
  echo "$LOG_PREFIX Google-Drive-Upload abgeschlossen."
else
  echo "$LOG_PREFIX Hinweis: rclone/gdrive-Remote noch nicht konfiguriert, kein Offsite-Upload."
fi

echo "$LOG_PREFIX Backup fertig."
