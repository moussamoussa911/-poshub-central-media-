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
   - `POS_HUB_API_KEY=<YOUR_STRONG_KEY>`
5. Attach a **Persistent Disk** mounted at `/var/data`.

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
