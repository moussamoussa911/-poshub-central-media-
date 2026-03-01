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
- `/var/data/static/menu_images` (uploaded images)
- `/var/data/*.db` (SQLite data)

## URL examples
- Health: `https://<service>.onrender.com/health`
- Static image: `https://<service>.onrender.com/static/menu_images/<file>`

## Important
All customers must use the same `online_url` (this Render service URL) to share one gallery.
