import type { NextConfig } from "next";
import path from "node:path";

// Where the static-exported app is mounted on the backend.
// Empty string = served at "/". "/app" = served at "/app/...".
const BASE_PATH = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

const nextConfig: NextConfig = {
  // Static export — emits HTML/JS/CSS into ./out, served by FastAPI.
  // The backend mounts ./out under BASE_PATH (and redirects /gallery-admin
  // to BASE_PATH for backwards compatibility).
  output: "export",
  trailingSlash: true,
  images: { unoptimized: true },

  basePath: BASE_PATH || undefined,
  assetPrefix: BASE_PATH || undefined,

  turbopack: {
    root: path.resolve(__dirname),
  },

  // NOTE: rewrites() / redirects() / headers() are unsupported with
  // `output: "export"`. For local dev, point NEXT_PUBLIC_API_BASE at the
  // backend (CORS is enabled on the backend for localhost:3000).
};

export default nextConfig;
