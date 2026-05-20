# Media Center — Frontend

Modern Next.js 16 + React 19 frontend for the POS-Hub Media Center.
Notion/Linear-inspired admin UI for browsing, organizing and uploading
shared menu images.

## Features

- **Gallery view** — image grid with categories sidebar, search, pagination
- **Bulk actions** — select many images, move/delete in one go
- **Image detail** — fullscreen preview, rename, move category, replace file, delete
- **Drag-and-drop upload** — multi-file with per-file name + category editing
- **Categories** — create, reorder (move up/down), delete
- **Team** — create/edit/delete admin and editor users
- **Branding** — set company name, tagline, logo URL, about text
- **Stats** — most-selected and most-downloaded leaderboards
- **Auth** — username/password or API-key recovery, session via `X-Gallery-Session` header (LocalStorage)
- **Mobile-friendly** — responsive layout with mobile drawer sidebar

## Local development

```bash
cd poshub-central-media/frontend
npm install
npm run dev
```

By default, requests are proxied via Next.js rewrites to
`https://poshub-central-media.onrender.com` (configured in `.env.local`),
so no CORS configuration is required on the backend for local testing.

To point at a different backend (e.g. local dev server) edit `.env.local`:

```dotenv
NEXT_PUBLIC_API_BASE=                       # empty = use proxy
API_BACKEND=http://localhost:8766           # proxy target
```

If you set `NEXT_PUBLIC_API_BASE` to a non-empty value, the frontend
talks **directly** to that base URL (no proxy). The backend must then
allow CORS for the frontend origin.

## Production deployment

Two patterns:

1. **Same-origin** (recommended): keep the proxy via `next.config.ts`
   rewrites. Frontend and backend are reached through the same domain,
   so cookies and headers work without extra CORS setup.

2. **Cross-origin**: set `NEXT_PUBLIC_API_BASE` at build time and
   configure CORS on the backend (already wired up — set
   `POS_HUB_CORS_ORIGINS=https://your-frontend.example.com`).

```bash
npm run build
npm run start
```

## Tech stack

- **Next.js 16** with App Router, Turbopack
- **React 19**
- **TypeScript 5**
- **Tailwind CSS 4** (with CSS-first `@theme` config)
- **TanStack Query 5** for server state
- **lucide-react** icons
- **class-variance-authority** + **tailwind-merge** for component variants

## Project layout

```
src/
├── app/
│   ├── layout.tsx              # root layout + providers
│   ├── page.tsx                # gallery (home)
│   ├── login/page.tsx          # password / API-key login
│   ├── upload/page.tsx         # drag-drop multi-file upload
│   └── settings/
│       ├── layout.tsx          # shared tabs nav
│       ├── team/page.tsx
│       ├── branding/page.tsx
│       ├── categories/page.tsx
│       └── stats/page.tsx
├── components/
│   ├── providers.tsx           # TanStack Query provider
│   ├── layout/
│   │   ├── app-shell.tsx       # sidebar + topbar + auth gate
│   │   ├── sidebar.tsx
│   │   └── topbar.tsx
│   ├── gallery/
│   │   ├── image-card.tsx
│   │   ├── image-detail.tsx
│   │   └── bulk-bar.tsx
│   └── ui/
│       ├── button.tsx
│       └── input.tsx
└── lib/
    ├── api.ts                  # API client + types
    ├── auth.ts                 # useAuth hook
    └── utils.ts                # cn(), formatBytes(), prettyCategory()
```

## Auth model

The frontend stores the session token in `localStorage` and sends it as
the `X-Gallery-Session` HTTP header on every request. This avoids
issues with the backend's `Secure=true` cookie (which is rejected over
plain HTTP localhost).

If a user logs in via API key, the key itself is also stored and sent
as `X-API-Key`, so requests still authenticate even if the session
token expires.

## Backend changes

`pos_hub_server.py` was modified to add `CORSMiddleware` (see top of
`create_app()`). Set `POS_HUB_CORS_ORIGINS` to a comma-separated list
of allowed origins, e.g.

```
POS_HUB_CORS_ORIGINS=https://media.example.com,https://staff.example.com
```

In local dev (with the Next proxy) this isn't needed.
