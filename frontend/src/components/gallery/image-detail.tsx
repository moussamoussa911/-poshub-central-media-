"use client";

import { useEffect, useRef, useState } from "react";
import { useMutation, useQueryClient } from "@tanstack/react-query";
import {
  GalleryItem,
  deleteItem,
  moveItem,
  renameItem,
  replaceItem,
  type CategoryItem,
} from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { X, Trash2, Replace, Copy, ExternalLink } from "lucide-react";
import { cn, formatBytes } from "@/lib/utils";

interface Props {
  item: GalleryItem;
  categories: CategoryItem[];
  onClose: () => void;
}

export function ImageDetail({ item, categories, onClose }: Props) {
  const qc = useQueryClient();
  const [newName, setNewName] = useState(
    item.name.replace(/\.(png|jpe?g|webp)$/i, ""),
  );
  const [newCategory, setNewCategory] = useState(item.category);
  const [busy, setBusy] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const fileInputRef = useRef<HTMLInputElement>(null);

  useEffect(() => {
    function onKey(e: KeyboardEvent) {
      if (e.key === "Escape") onClose();
    }
    window.addEventListener("keydown", onKey);

    // Lock background scroll while modal is open.
    // We use position:fixed + saved scrollY so the page can't scroll behind
    // and we restore the exact scroll position when the modal closes.
    const scrollY = window.scrollY;
    const prevBody = {
      position: document.body.style.position,
      top: document.body.style.top,
      width: document.body.style.width,
      overflow: document.body.style.overflow,
    };
    const prevHtmlOverflow = document.documentElement.style.overflow;
    document.body.style.position = "fixed";
    document.body.style.top = `-${scrollY}px`;
    document.body.style.width = "100%";
    document.body.style.overflow = "hidden";
    document.documentElement.style.overflow = "hidden";

    return () => {
      window.removeEventListener("keydown", onKey);
      document.body.style.position = prevBody.position;
      document.body.style.top = prevBody.top;
      document.body.style.width = prevBody.width;
      document.body.style.overflow = prevBody.overflow;
      document.documentElement.style.overflow = prevHtmlOverflow;
      window.scrollTo(0, scrollY);
    };
  }, [onClose]);

  function invalidate() {
    qc.invalidateQueries({ queryKey: ["gallery"] });
    qc.invalidateQueries({ queryKey: ["categories"] });
  }

  const renameMut = useMutation({
    mutationFn: () => renameItem(item.rel_path, newName.trim()),
    onSuccess: () => {
      invalidate();
      onClose();
    },
    onError: (e: Error) => setError(e.message),
  });

  const moveMut = useMutation({
    mutationFn: () => moveItem(item.rel_path, newCategory),
    onSuccess: () => {
      invalidate();
      onClose();
    },
    onError: (e: Error) => setError(e.message),
  });

  const deleteMut = useMutation({
    mutationFn: () => deleteItem(item.rel_path),
    onSuccess: () => {
      invalidate();
      onClose();
    },
    onError: (e: Error) => setError(e.message),
  });

  async function onReplace(file: File) {
    setError(null);
    setBusy("replace");
    try {
      await replaceItem(item.rel_path, file);
      invalidate();
      onClose();
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e));
    } finally {
      setBusy(null);
    }
  }

  return (
    <div
      className="fixed inset-0 z-50 grid grid-cols-1 md:grid-cols-[1fr_400px] grid-rows-[auto_1fr] md:grid-rows-1 bg-black/40 backdrop-blur-sm overflow-hidden overscroll-contain"
      onClick={onClose}
      onWheel={(e) => e.stopPropagation()}
      onTouchMove={(e) => e.stopPropagation()}
    >
      <div
        className="hidden md:grid place-items-center p-4 md:p-12 overflow-hidden"
        onClick={(e) => e.stopPropagation()}
      >
        {/* eslint-disable-next-line @next/next/no-img-element */}
        <img
          src={item.url}
          alt={item.name}
          className="max-h-full max-w-full rounded-lg shadow-2xl object-contain bg-white"
        />
      </div>

      {/* Mobile-only smaller preview at the top */}
      <div
        className="md:hidden grid place-items-center p-4 max-h-[40vh] bg-black/20"
        onClick={(e) => e.stopPropagation()}
      >
        {/* eslint-disable-next-line @next/next/no-img-element */}
        <img
          src={item.url}
          alt={item.name}
          className="max-h-full max-w-full rounded-lg shadow-xl object-contain bg-white"
        />
      </div>

      <aside
        className="bg-white border-l border-[var(--color-border)] flex flex-col overflow-y-auto overscroll-contain h-full max-h-screen"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="px-5 h-14 flex items-center justify-between border-b border-[var(--color-border)] sticky top-0 bg-white">
          <div className="text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
            Image
          </div>
          <Button variant="ghost" size="icon" onClick={onClose}>
            <X className="size-4" />
          </Button>
        </div>

        <div className="px-5 py-4 space-y-5">
          <div>
            <div className="text-sm font-medium break-words">{item.name}</div>
            <div className="mt-1 text-xs text-[var(--color-text-subtle)] tabular-nums">
              {formatBytes(item.size)} · {item.category}
            </div>
          </div>

          <div>
            <label className="text-xs text-[var(--color-text-muted)]">
              Rename
            </label>
            <div className="mt-1 flex gap-2">
              <Input
                value={newName}
                onChange={(e) => setNewName(e.target.value)}
              />
              <Button
                variant="primary"
                size="sm"
                disabled={renameMut.isPending || !newName.trim()}
                onClick={() => renameMut.mutate()}
              >
                {renameMut.isPending ? "Saving" : "Save"}
              </Button>
            </div>
          </div>

          <div>
            <label className="text-xs text-[var(--color-text-muted)]">
              Move to category
            </label>
            <div className="mt-1 flex gap-2">
              <select
                value={newCategory}
                onChange={(e) => setNewCategory(e.target.value)}
                className="h-9 flex-1 rounded-md border border-[var(--color-border)] bg-white px-3 text-sm"
              >
                {categories.map((c) => (
                  <option key={c.name} value={c.name}>
                    {c.name}
                  </option>
                ))}
              </select>
              <Button
                variant="secondary"
                size="sm"
                disabled={moveMut.isPending || newCategory === item.category}
                onClick={() => moveMut.mutate()}
              >
                {moveMut.isPending ? "Moving" : "Move"}
              </Button>
            </div>
          </div>

          <div>
            <label className="text-xs text-[var(--color-text-muted)]">
              Replace file
            </label>
            <div className="mt-1 flex gap-2">
              <input
                ref={fileInputRef}
                type="file"
                accept="image/*"
                className="hidden"
                onChange={(e) => {
                  const f = e.target.files?.[0];
                  if (f) onReplace(f);
                }}
              />
              <Button
                variant="secondary"
                size="sm"
                className="w-full"
                onClick={() => fileInputRef.current?.click()}
                disabled={busy === "replace"}
              >
                <Replace className="size-3.5" />
                {busy === "replace" ? "Uploading…" : "Choose new file"}
              </Button>
            </div>
          </div>

          <div className="border-t border-[var(--color-border)] pt-4 space-y-2">
            <a
              href={item.url}
              target="_blank"
              rel="noreferrer"
              className="flex items-center gap-2 text-xs text-[var(--color-accent)] hover:underline"
            >
              <ExternalLink className="size-3.5" />
              Open original
            </a>
            <button
              type="button"
              onClick={() => navigator.clipboard.writeText(item.url)}
              className="flex items-center gap-2 text-xs text-[var(--color-text-muted)] hover:text-[var(--color-text)]"
            >
              <Copy className="size-3.5" />
              Copy URL
            </button>
            <div
              className={cn(
                "text-[10px] font-mono break-all bg-[var(--color-bg-subtle)] border border-[var(--color-border)] rounded px-2 py-1.5 text-[var(--color-text-muted)]",
              )}
            >
              {item.url}
            </div>
          </div>

          {error && (
            <div className="text-sm rounded-md border border-[var(--color-danger)] bg-[var(--color-danger-bg)] text-[var(--color-danger)] px-3 py-2">
              {error}
            </div>
          )}

          <div className="border-t border-[var(--color-border)] pt-4">
            <Button
              variant="danger"
              size="sm"
              className="w-full"
              onClick={() => {
                if (confirm(`Delete "${item.name}"? This cannot be undone.`))
                  deleteMut.mutate();
              }}
              disabled={deleteMut.isPending}
            >
              <Trash2 className="size-3.5" />
              {deleteMut.isPending ? "Deleting…" : "Delete image"}
            </Button>
          </div>
        </div>
      </aside>
    </div>
  );
}
