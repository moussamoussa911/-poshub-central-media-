import type { NextConfig } from "next";
import path from "node:path";

const API_BACKEND =
  process.env.API_BACKEND ?? "https://poshub-central-media.onrender.com";

const nextConfig: NextConfig = {
  turbopack: {
    root: path.resolve(__dirname),
  },
  images: {
    remotePatterns: [
      { protocol: "https", hostname: "poshub-central-media.onrender.com" },
      { protocol: "http", hostname: "localhost" },
      { protocol: "http", hostname: "127.0.0.1" },
    ],
  },
  async rewrites() {
    return [
      { source: "/api/:path*", destination: `${API_BACKEND}/api/:path*` },
      { source: "/gallery-admin/:path*", destination: `${API_BACKEND}/gallery-admin/:path*` },
      { source: "/static/:path*", destination: `${API_BACKEND}/static/:path*` },
    ];
  },
};

export default nextConfig;
