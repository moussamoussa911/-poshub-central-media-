"use client";

import { useMemo, useState } from "react";
import { useQuery } from "@tanstack/react-query";
import { ApiError, listCategories, listGallery, type GalleryItem } from "@/lib/api";
import { AppShell } from "@/components/layout/app-shell";
import { ImageCard } from "@/components/gallery/image-card";
import { ImageDetail } from "@/components/gallery/image-detail";
import { BulkBar } from "@/components/gallery/bulk-bar";
import { Button } from "@/components/ui/button";
import { CheckSquare, Square, ChevronLeft, ChevronRight, Loader2 } from "lucide-react";
import { prettyCategory } from "@/lib/utils";
import Link from "next/link";

export default function GalleryPage() {
  const [category, setCategory] = useState("all");
  const [search, setSearch] = useState("");
  const [page, setPage] = useState(1);
  const [selected, setSelected] = useState<Set<string>>(new Set());
  const [openItem, setOpenItem] = useState<GalleryItem | null>(null);
  const [selectionMode, setSelectionMode] = useState(false);

  const galleryQ = useQuery({
    queryKey: ["gallery", category, search, page],
    queryFn: () => listGallery({ category, q: search, page, pageSize: 60 }),
  });

  const catsQ = useQuery({
    queryKey: ["categories"],
    queryFn: listCategories,
  });

  const cats = catsQ.data?.items ?? [];
  const items = galleryQ.data?.items ?? [];

  function toggle(rel: string) {
    setSelected((prev) => {
      const next = new Set(prev);
      if (next.has(rel)) next.delete(rel);
      else next.add(rel);
      return next;
    });
  }

  function selectAll() {
    setSelected(new Set(items.map((i) => i.rel_path)));
    setSelectionMode(true);
  }

  function clearSelection() {
    setSelected(new Set());
    setSelectionMode(false);
  }

  const totalPages = galleryQ.data?.total_pages ?? 1;

  const headerExtras = useMemo(
    () => (
      <div className="hidden md:flex items-center gap-2">
        <Button
          variant={selectionMode ? "primary" : "ghost"}
          size="sm"
          onClick={() => {
            if (selectionMode) clearSelection();
            else setSelectionMode(true);
          }}
        >
          {selectionMode ? (
            <CheckSquare className="size-4" />
          ) : (
            <Square className="size-4" />
          )}
          {selectionMode ? "Selecting" : "Select"}
        </Button>
        {selectionMode && (
          <Button variant="ghost" size="sm" onClick={selectAll}>
            All
          </Button>
        )}
        <Link href="/upload">
          <Button variant="primary" size="sm">
            Upload
          </Button>
        </Link>
      </div>
    ),
    [selectionMode],
  );

  return (
    <AppShell
      activeCategory={category}
      onSelectCategory={(c) => {
        setCategory(c);
        setPage(1);
        clearSelection();
      }}
      search={search}
      onSearchChange={(v) => {
        setSearch(v);
        setPage(1);
      }}
      topbarExtras={headerExtras}
    >
      <div className="px-4 md:px-8 py-6">
        <div className="flex items-end justify-between mb-5">
          <div>
            <div className="text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
              {galleryQ.data?.total ?? 0} images
            </div>
            <h1 className="mt-1 text-2xl font-semibold tracking-tight">
              {prettyCategory(category)}
            </h1>
          </div>
        </div>

        {galleryQ.isLoading ? (
          <div className="grid place-items-center py-16 text-[var(--color-text-muted)] text-sm">
            <Loader2 className="size-5 animate-spin mr-2" />
            Loading…
          </div>
        ) : galleryQ.isError ? (
          <div className="text-sm rounded-md border border-[var(--color-danger)] bg-[var(--color-danger-bg)] text-[var(--color-danger)] p-4 flex items-start justify-between gap-3">
            <div>
              {galleryQ.error instanceof ApiError && galleryQ.error.status === 429 ? (
                <>
                  <div className="font-medium">Slow down — rate limit reached.</div>
                  <div className="mt-1 text-xs opacity-80">
                    The server briefly capped requests from your IP. Wait a few seconds, then retry.
                  </div>
                </>
              ) : (
                <>Failed to load: {(galleryQ.error as Error)?.message}</>
              )}
            </div>
            <Button
              variant="outline"
              size="sm"
              onClick={() => galleryQ.refetch()}
              disabled={galleryQ.isFetching}
            >
              Retry
            </Button>
          </div>
        ) : items.length === 0 ? (
          <div className="text-center py-16 text-[var(--color-text-muted)]">
            <div className="text-sm">No images here yet.</div>
            <Link
              href="/upload"
              className="mt-3 inline-block text-sm text-[var(--color-accent)] hover:underline"
            >
              Upload your first image →
            </Link>
          </div>
        ) : (
          <>
            <div className="grid grid-cols-2 sm:grid-cols-3 md:grid-cols-4 lg:grid-cols-5 xl:grid-cols-6 gap-3">
              {items.map((item) => (
                <ImageCard
                  key={item.rel_path}
                  item={item}
                  selected={selected.has(item.rel_path)}
                  selectionMode={selectionMode}
                  onToggleSelect={() => toggle(item.rel_path)}
                  onOpen={() => setOpenItem(item)}
                />
              ))}
            </div>

            {totalPages > 1 && (
              <div className="mt-8 flex items-center justify-center gap-2 text-sm">
                <Button
                  variant="ghost"
                  size="sm"
                  disabled={page <= 1}
                  onClick={() => setPage((p) => Math.max(1, p - 1))}
                >
                  <ChevronLeft className="size-4" /> Prev
                </Button>
                <span className="px-3 text-[var(--color-text-muted)] tabular-nums">
                  {page} / {totalPages}
                </span>
                <Button
                  variant="ghost"
                  size="sm"
                  disabled={page >= totalPages}
                  onClick={() =>
                    setPage((p) => Math.min(totalPages, p + 1))
                  }
                >
                  Next <ChevronRight className="size-4" />
                </Button>
              </div>
            )}
          </>
        )}
      </div>

      <BulkBar
        selected={Array.from(selected)}
        categories={cats}
        onClear={clearSelection}
      />

      {openItem && (
        <ImageDetail
          item={openItem}
          categories={cats}
          onClose={() => setOpenItem(null)}
        />
      )}
    </AppShell>
  );
}
