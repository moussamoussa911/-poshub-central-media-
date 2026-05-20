"use client";

import { useCallback, useRef, useState } from "react";
import { useQuery, useQueryClient } from "@tanstack/react-query";
import { AppShell } from "@/components/layout/app-shell";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { listCategories, uploadImage, renameItem, moveItem } from "@/lib/api";
import { cn, formatBytes } from "@/lib/utils";
import { CloudUpload, Trash2, X, CheckCircle2, AlertCircle, Loader2 } from "lucide-react";
import Link from "next/link";

type Status = "queued" | "uploading" | "done" | "error";

interface PendingItem {
  id: string;
  file: File;
  preview: string;
  name: string; // displayed/edited name (without extension)
  category: string;
  status: Status;
  error?: string;
  result?: { rel_path: string; url: string; duplicate?: boolean };
}

function makeId() {
  return Math.random().toString(36).slice(2);
}

function nameFromFile(file: File): string {
  return file.name.replace(/\.(png|jpe?g|webp)$/i, "");
}

export default function UploadPage() {
  const qc = useQueryClient();
  const catsQ = useQuery({ queryKey: ["categories"], queryFn: listCategories });
  const cats = catsQ.data?.items ?? [];

  const [pending, setPending] = useState<PendingItem[]>([]);
  const [defaultCategory, setDefaultCategory] = useState("all");
  const [isDragging, setIsDragging] = useState(false);
  const [running, setRunning] = useState(false);
  const fileInputRef = useRef<HTMLInputElement>(null);

  const addFiles = useCallback(
    (files: FileList | File[]) => {
      const list = Array.from(files).filter((f) => f.type.startsWith("image/"));
      const items: PendingItem[] = list.map((f) => ({
        id: makeId(),
        file: f,
        preview: URL.createObjectURL(f),
        name: nameFromFile(f),
        category: defaultCategory,
        status: "queued",
      }));
      setPending((p) => [...p, ...items]);
    },
    [defaultCategory],
  );

  function removeItem(id: string) {
    setPending((p) => {
      const x = p.find((i) => i.id === id);
      if (x) URL.revokeObjectURL(x.preview);
      return p.filter((i) => i.id !== id);
    });
  }

  function clearDone() {
    setPending((p) => p.filter((i) => i.status !== "done"));
  }

  function updateItem(id: string, patch: Partial<PendingItem>) {
    setPending((p) => p.map((i) => (i.id === id ? { ...i, ...patch } : i)));
  }

  function onDrop(e: React.DragEvent) {
    e.preventDefault();
    setIsDragging(false);
    if (e.dataTransfer.files?.length) addFiles(e.dataTransfer.files);
  }

  async function uploadOne(item: PendingItem): Promise<PendingItem> {
    updateItem(item.id, { status: "uploading" });
    try {
      // 1) Upload (file ends up under "all/" or chosen category with uuid name)
      const up = await uploadImage(item.file, item.category, item.file.name);
      let rel = `${up.category}/${up.filename}`;

      // 2) Optional rename
      const desired = item.name.trim();
      if (desired && desired !== up.filename.replace(/\.[^.]+$/, "")) {
        try {
          const r = await renameItem(rel, desired);
          rel = r.rel_path;
        } catch {
          // keep upload, name will remain
        }
      }

      // 3) Optional category move (if user changed it after upload + server placed elsewhere)
      const targetCat = item.category || "all";
      if (rel.split("/")[0] !== targetCat) {
        try {
          const m = await moveItem(rel, targetCat);
          rel = m.rel_path;
        } catch {
          // ignore
        }
      }

      const next: PendingItem = {
        ...item,
        status: "done",
        result: { rel_path: rel, url: up.image_url, duplicate: up.duplicate },
      };
      updateItem(item.id, next);
      return next;
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      updateItem(item.id, { status: "error", error: msg });
      return { ...item, status: "error", error: msg };
    }
  }

  async function uploadAll() {
    setRunning(true);
    const queue = pending.filter((i) => i.status === "queued" || i.status === "error");
    for (const it of queue) {
      // eslint-disable-next-line no-await-in-loop
      await uploadOne(it);
    }
    qc.invalidateQueries({ queryKey: ["gallery"] });
    qc.invalidateQueries({ queryKey: ["categories"] });
    setRunning(false);
  }

  const doneCount = pending.filter((p) => p.status === "done").length;
  const queueCount = pending.filter((p) => p.status === "queued" || p.status === "error").length;

  return (
    <AppShell activeCategory="all" onSelectCategory={() => {}}>
      <div className="px-4 md:px-8 py-6 max-w-5xl mx-auto">
        <div className="text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
          Upload
        </div>
        <h1 className="mt-1 text-2xl font-semibold tracking-tight">Add new images</h1>
        <p className="mt-1 text-sm text-[var(--color-text-muted)]">
          Drop files anywhere on this page, then review names and categories before uploading.
        </p>

        {/* Default category */}
        <div className="mt-6 flex items-end gap-3 flex-wrap">
          <div>
            <label className="text-xs text-[var(--color-text-muted)]">
              Default category
            </label>
            <select
              value={defaultCategory}
              onChange={(e) => setDefaultCategory(e.target.value)}
              className="mt-1 h-9 rounded-md border border-[var(--color-border)] bg-white px-3 text-sm min-w-[180px]"
            >
              {cats.map((c) => (
                <option key={c.name} value={c.name}>
                  {c.name}
                </option>
              ))}
            </select>
          </div>
          <Button
            variant="secondary"
            size="md"
            onClick={() => fileInputRef.current?.click()}
          >
            <CloudUpload className="size-4" />
            Choose files
          </Button>
          <input
            ref={fileInputRef}
            type="file"
            accept="image/*"
            multiple
            className="hidden"
            onChange={(e) => {
              if (e.target.files?.length) addFiles(e.target.files);
              e.target.value = "";
            }}
          />
        </div>

        {/* Drop zone */}
        <div
          onDragOver={(e) => {
            e.preventDefault();
            setIsDragging(true);
          }}
          onDragLeave={() => setIsDragging(false)}
          onDrop={onDrop}
          className={cn(
            "mt-5 rounded-xl border-2 border-dashed p-10 text-center transition-colors",
            isDragging
              ? "border-[var(--color-accent)] bg-blue-50/40"
              : "border-[var(--color-border-strong)] bg-[var(--color-bg-subtle)]",
          )}
        >
          <CloudUpload className="size-8 mx-auto text-[var(--color-text-subtle)]" />
          <div className="mt-2 text-sm">
            <span className="font-medium">Drag & drop images here</span>{" "}
            <span className="text-[var(--color-text-muted)]">or use Choose files</span>
          </div>
          <div className="text-xs text-[var(--color-text-subtle)] mt-1">
            PNG · JPG · WEBP — up to 15 MB each
          </div>
        </div>

        {/* Queue header */}
        {pending.length > 0 && (
          <div className="mt-8 flex items-center justify-between">
            <div className="text-sm text-[var(--color-text-muted)]">
              {pending.length} file{pending.length === 1 ? "" : "s"} ·{" "}
              {doneCount} done · {queueCount} pending
            </div>
            <div className="flex items-center gap-2">
              {doneCount > 0 && (
                <Button variant="ghost" size="sm" onClick={clearDone}>
                  Clear done
                </Button>
              )}
              <Button
                variant="primary"
                size="md"
                disabled={queueCount === 0 || running}
                onClick={uploadAll}
              >
                {running ? (
                  <Loader2 className="size-4 animate-spin" />
                ) : (
                  <CloudUpload className="size-4" />
                )}
                {running ? "Uploading…" : `Upload ${queueCount}`}
              </Button>
            </div>
          </div>
        )}

        {/* Pending items */}
        {pending.length > 0 && (
          <div className="mt-4 grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-3">
            {pending.map((it) => (
              <div
                key={it.id}
                className="rounded-lg border border-[var(--color-border)] bg-white overflow-hidden"
              >
                <div className="aspect-video bg-[var(--color-bg-subtle)] relative">
                  {/* eslint-disable-next-line @next/next/no-img-element */}
                  <img
                    src={it.preview}
                    alt={it.file.name}
                    className="w-full h-full object-cover"
                  />
                  <button
                    onClick={() => removeItem(it.id)}
                    className="absolute top-2 right-2 size-7 grid place-items-center bg-white/90 rounded-full shadow hover:bg-white"
                    aria-label="Remove"
                  >
                    <X className="size-4" />
                  </button>
                  {it.status === "done" && (
                    <div className="absolute bottom-2 left-2 bg-[var(--color-success)] text-white text-xs rounded px-1.5 py-0.5 flex items-center gap-1">
                      <CheckCircle2 className="size-3" />
                      Uploaded
                    </div>
                  )}
                  {it.status === "error" && (
                    <div className="absolute bottom-2 left-2 bg-[var(--color-danger)] text-white text-xs rounded px-1.5 py-0.5 flex items-center gap-1">
                      <AlertCircle className="size-3" />
                      Failed
                    </div>
                  )}
                  {it.status === "uploading" && (
                    <div className="absolute inset-0 grid place-items-center bg-black/40 text-white text-xs">
                      <Loader2 className="size-5 animate-spin" />
                    </div>
                  )}
                </div>
                <div className="p-3 space-y-2">
                  <Input
                    value={it.name}
                    onChange={(e) => updateItem(it.id, { name: e.target.value })}
                    placeholder="image_name"
                    disabled={it.status === "uploading" || it.status === "done"}
                    className="text-xs"
                  />
                  <select
                    value={it.category}
                    onChange={(e) =>
                      updateItem(it.id, { category: e.target.value })
                    }
                    disabled={it.status === "uploading" || it.status === "done"}
                    className="h-8 w-full rounded-md border border-[var(--color-border)] bg-white px-2 text-xs disabled:opacity-50"
                  >
                    {cats.map((c) => (
                      <option key={c.name} value={c.name}>
                        {c.name}
                      </option>
                    ))}
                  </select>
                  <div className="flex items-center justify-between text-[10px] text-[var(--color-text-subtle)]">
                    <span className="truncate">{it.file.name}</span>
                    <span className="tabular-nums">
                      {formatBytes(it.file.size)}
                    </span>
                  </div>
                  {it.error && (
                    <div className="text-xs text-[var(--color-danger)]">
                      {it.error}
                    </div>
                  )}
                  {it.result && (
                    <a
                      href={it.result.url}
                      target="_blank"
                      rel="noreferrer"
                      className="block text-[10px] font-mono break-all text-[var(--color-accent)] hover:underline"
                    >
                      {it.result.rel_path}
                      {it.result.duplicate ? " (duplicate)" : ""}
                    </a>
                  )}
                </div>
              </div>
            ))}
          </div>
        )}

        {pending.length === 0 && (
          <div className="mt-12 text-center text-sm text-[var(--color-text-muted)]">
            No files queued yet.{" "}
            <Link href="/" className="text-[var(--color-accent)] hover:underline">
              Back to gallery
            </Link>
          </div>
        )}
      </div>
    </AppShell>
  );
}
