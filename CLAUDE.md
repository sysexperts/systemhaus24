# Systemhaus24 – itool

Internes CRM/ERP-Tool ("itool") für Systemhaus24, ein IT-Dienstleister. Flask + PostgreSQL + Docker,
live unter https://tools.systemhaus24.net. Alle UI-Texte sind auf Deutsch.

## Projektstruktur

- Der gesamte Code liegt im Unterordner `itool/` (Flask-App `app.py`, DB-Setup `database.py`,
  Templates in `itool/templates/`, Docker-Setup `itool/docker-compose.yml`).
- GitHub-Repo: https://github.com/sysexperts/systemhaus24, Branch `master`.

## Deploy-Pipeline

Änderungen werden **nie** direkt auf dem Server bearbeitet. Immer:

1. Lokal in `itool/` ändern.
2. `git add`, `git commit`, `git push origin master`.
3. Per SSH auf den Server (`root@31.70.108.144`, PuTTY `plink`/`pscp`):
   ```
   cd /opt/systemhaus24 && git pull origin master && cd itool && docker compose up -d --build
   ```
4. **Danach immer prüfen, nicht nur deployen:**
   - `docker logs itool-itool-1 --tail 30` auf Fehler checken.
   - Kernseiten regressionstesten (z.B. via Flask-Test-Client mit korrekt gesetzter Session:
     `sess['user_id']`, `sess['username']`, `sess['role']` – alle drei nötig, sonst 302-Redirect zum Login).
   - Erst danach dem Nutzer "fertig" melden.

Der itool-Container ist nur auf `127.0.0.1:5000` gebunden (nginx-Reverse-Proxy davor) – **niemals**
auf `0.0.0.0` oder öffentlichen Port ändern, das war schon mal ein Sicherheitsregression-Bug.

DB-Zugangsdaten liegen in der (gitignored) `.env` auf dem Server, nicht im `docker-compose.yml`
hardcoden. Volume heißt `itool_dbdata` – beim Anfassen von `docker-compose.yml` sicherstellen, dass
kein Volume-Rename passiert (sonst Datenverlust).

## Backups

- Skript: `/opt/systemhaus24/backup-db.sh` auf dem Server, läuft täglich um 3:30 Uhr per Cron
  (`crontab -l` als root).
- Sichert DB-Dump (`pg_dump` aus `itool-db-1`) und den `itool/data`-Ordner (Dokumente/Uploads).
- Struktur lokal **und** auf Google Drive identisch: `backups/YYYY-MM-DD/db_<timestamp>.sql.gz`
  und `backups/YYYY-MM-DD/data_<timestamp>.tar.gz`.
- Lokal unter `/opt/systemhaus24/backups/`, extern via `rclone` auf Google Drive im Ordner
  `gdrive:itool-backups/`.
- **Kein automatisches Lösch-/Retention-Limit** – der Nutzer räumt manuell auf. Beim Anfassen des
  Skripts diese bewusste Entscheidung nicht wieder durch eine automatische Aufräumroutine ersetzen,
  ohne vorher zu fragen.
- rclone-Config mit Google-Drive-Token liegt in `/root/.config/rclone/rclone.conf` auf dem Server
  (nicht im Git-Repo, nicht anfassen ohne Grund).

## Feste Konventionen

- **GoBD-Prinzip**: Rechnungen und Verträge, die bereits versendet/unterschrieben sind, werden
  **nicht gelöscht**, sondern storniert (Status `cancelled`). Löschen ist nur im Entwurfsstatus erlaubt.
- **Datumsformat**: TT.MM.YYYY in der UI. Dafür die Jinja-Filter `fmtdt`/`fmtdate` benutzen, nie
  roh auf `datetime`-Objekten slicen (`obj[:16]` wirft `TypeError`).
- **PDF-Erzeugung**: über xhtml2pdf, Templates die *nicht* `base.html` erweitern (z.B. `contract_pdf.html`,
  `invoice_pdf.html`). Diese bekommen die Akzentfarbe nicht automatisch – `cfg.get('accent_color', '#1c3461')`
  muss explizit in den Template-Kontext und im `<style>`-Block inline eingesetzt werden (kein `var()`,
  xhtml2pdf unterstützt das nicht zuverlässig).
- **Downloads statt Browser-Print**: Für Verträge/Rechnungen echte PDF-Download-Links (`/contracts/<id>/pdf`,
  `/invoices/<id>/pdf`) verwenden, nicht `window.print()` – der Browser-Druckdialog fügt eigene
  Kopf-/Fußzeilen (URL, Datum, Seitenzahl) hinzu, die nicht Teil des Dokuments sein sollen.
- **Firmenname im Tool ist "Systemhaus24"**, nicht "tkToolkit" – dieser Name wurde entfernt und
  darf nicht wieder auftauchen (Seitentitel, SMTP-Absendername, Fehlermeldungen).
- Layout-Einstellungen (Akzentfarbe, Logo, Chat-Position) liegen im `app_cfg`/`cfg`-Objekt und werden
  über die Einstellungen → Layout-Tab verwaltet. `shade_hex(hex, factor)` ist als Jinja-Global für
  hellere/dunklere Farbvarianten registriert.

## Bekannte Fallstricke

- **Jinja `Markup.replace()`-Falle**: `{{ text | e | replace('\n', '<br>') | safe }}` ist kaputt –
  nach `|e` ist der Wert ein `Markup`-Objekt, dessen `.replace()` den Ersatzstring (`<br>`) selbst wieder
  escaped, wodurch literales `<br>` im Output erscheint. Stattdessen zeilenweise loopen:
  `{% for line in text.split('\n') %}{{ line }}{% if not loop.last %}<br>{% endif %}{% endfor %}`.
- **xhtml2pdf-Tabellenlayout**: Prozentbreiten gemischt mit schmalen Trennspalten (z.B. 1px Divider)
  können zu `ValueError: negative availWidth` führen. Feste `pt`-Breiten statt Prozent verwenden.
- **Flash-Messages**: `base.html` rendert `get_flashed_messages()` bereits zentral im `<main>`-Block.
  Einzelne Content-Templates dürfen das **nicht** nochmal selbst tun, sonst erscheinen Erfolgsmeldungen
  doppelt. Ausnahme: eigenständige Seiten außerhalb von `base.html` (Login, Setup, Promoter-Registrierung).

## Umgang mit Server-Änderungen

Falls der Server-Stand vom lokalen Git-Stand abweicht (z.B. weil parallel auf einem anderen Rechner
direkt am Server gearbeitet wurde): **niemals** den Server einfach zurücksetzen oder Änderungen
verwerfen, ohne vorher zu prüfen, ob dort eigenständige, noch nicht committete Arbeit liegt. Im
Zweifel nachfragen, bevor mit `git reset --hard` oder `git merge --abort` gearbeitet wird.

## Qualitätsanspruch

Fehler aus den Docker-Logs werden ernst genommen – nach jedem Deploy aktiv auf Fehler prüfen, nicht
warten bis der Nutzer sie meldet. Da die Software wächst und nicht bei jeder Änderung alle Funktionen
manuell getestet werden können, nach relevanten Änderungen eine kurze Regressionsprüfung der
betroffenen und angrenzenden Seiten durchführen, bevor eine Aufgabe als erledigt gemeldet wird.
