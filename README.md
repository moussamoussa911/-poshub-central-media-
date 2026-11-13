# poshub-central-media

Central POS-Hub backend for shared menu image gallery across all customers.

## Files
- `pos_hub_server.py` - API server and static file hosting
- `poshub_runtime.py` - optional runtime loader used by server
- `requirements.txt` - minimal dependencies

## Render setup (Web Service)
1. Create **New Web Service** from this repo.
2. Build command:
   - `pip install -r requirements.txt`
3. Start command:
   - `python pos_hub_server.py`
4. Add env vars:
   - `POS_HUB_DATA_DIR=/var/data`
   - `POS_HUB_PUBLIC_SCHEME=https`
   - `POS_HUB_API_KEY=<YOUR_STRONG_KEY>` (master key: gallery admin, scripts; required,
     on Render it is never read from a file)
   - `POS_HUB_GALLERY_ADMIN_PASSWORD=<at least 12 characters>` (owner of the gallery admin;
     required, the service does not start without it)
   - `POS_HUB_CLIENT_KEYS=<key1>,<key2>` (optional: keys of the tills; they may read the
     gallery, upload, search photos and track picks, nothing else)
5. Attach a **Persistent Disk** mounted at `/var/data`.

`poshub_runtime.json` (local runs only) is ignored by git and must never be committed.

## What is stored on disk
- `/var/data/static/global_gallery` (uploaded shared gallery images)
- `/var/data/static/menu_images` (legacy/backward-compat path)
- `/var/data/*.db` (SQLite data)

## URL examples
- Health: `https://<service>.onrender.com/health`
- Static image: `https://<service>.onrender.com/static/global_gallery/<category>/<file>`
- Admin GUI: `https://<service>.onrender.com/gallery-admin`
  - username/password login with session cookie
  - admin user management (create/edit/delete team accounts)
  - branding panel (company name, tagline, logo URL, about text)
  - categories with order, thumbnails, create/delete
  - multi-file/folder upload + drag/drop
  - rename/replace image
  - single and batch move/delete
  - pagination + search

## Important
All customers must use the same `online_url` (this Render service URL) to share one gallery.
