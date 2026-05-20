"use client";

import { useQuery } from "@tanstack/react-query";
import { API_BASE } from "@/lib/api";
import { Loader2 } from "lucide-react";

interface TopItem {
  rel_path: string;
  url: string;
  selected_count: number;
  downloaded_count: number;
  last_selected_at?: string;
  last_downloaded_at?: string;
}

async function fetchTop(metric: "selected" | "downloaded"): Promise<{
  ok: boolean;
  metric: string;
  items: TopItem[];
}> {
  const token =
    typeof window !== "undefined"
      ? window.localStorage.getItem("mc.session")
      : null;
  const apiKey =
    typeof window !== "undefined"
      ? window.localStorage.getItem("mc.apikey")
      : null;
  const headers: Record<string, string> = {};
  if (token) headers["X-Gallery-Session"] = token;
  if (apiKey) headers["X-API-Key"] = apiKey;
  const base = API_BASE || "";
  const res = await fetch(`${base}/api/gallery/stats/top?metric=${metric}&limit=10`, {
    headers,
  });
  return res.json();
}

export default function StatsPage() {
  const selectedQ = useQuery({
    queryKey: ["stats", "selected"],
    queryFn: () => fetchTop("selected"),
  });
  const downloadedQ = useQuery({
    queryKey: ["stats", "downloaded"],
    queryFn: () => fetchTop("downloaded"),
  });

  function Block({
    title,
    items,
    metric,
    loading,
  }: {
    title: string;
    items: TopItem[];
    metric: "selected_count" | "downloaded_count";
    loading: boolean;
  }) {
    return (
      <div>
        <h2 className="text-sm font-medium mb-2">{title}</h2>
        <div className="rounded-lg border border-[var(--color-border)] bg-white overflow-hidden">
          {loading ? (
            <div className="p-4 text-sm text-[var(--color-text-muted)]">
              <Loader2 className="size-4 inline animate-spin mr-2" />
              Loading…
            </div>
          ) : items.length === 0 ? (
            <div className="p-4 text-sm text-[var(--color-text-muted)]">
              No data yet.
            </div>
          ) : (
            items.map((it, i) => (
              <div
                key={it.rel_path}
                className="flex items-center gap-3 px-3 py-2 border-b last:border-b-0 border-[var(--color-border)]"
              >
                <span className="size-6 text-xs text-[var(--color-text-subtle)] tabular-nums grid place-items-center">
                  {i + 1}
                </span>
                {/* eslint-disable-next-line @next/next/no-img-element */}
                <img
                  src={it.url}
                  alt=""
                  className="size-10 rounded object-cover bg-[var(--color-bg-subtle)]"
                />
                <div className="flex-1 min-w-0">
                  <div className="text-sm truncate">{it.rel_path}</div>
                </div>
                <div className="text-sm font-medium tabular-nums">{it[metric]}</div>
              </div>
            ))
          )}
        </div>
      </div>
    );
  }

  return (
    <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
      <Block
        title="Most selected"
        items={selectedQ.data?.items ?? []}
        metric="selected_count"
        loading={selectedQ.isLoading}
      />
      <Block
        title="Most downloaded"
        items={downloadedQ.data?.items ?? []}
        metric="downloaded_count"
        loading={downloadedQ.isLoading}
      />
    </div>
  );
}
