"use client";

import { type GalleryItem } from "@/lib/api";
import { cn, formatBytes, prettyCategory } from "@/lib/utils";
import { Check } from "lucide-react";

interface Props {
  item: GalleryItem;
  selected: boolean;
  selectionMode: boolean;
  onToggleSelect: () => void;
  onOpen: () => void;
}

export function ImageCard({
  item,
  selected,
  selectionMode,
  onToggleSelect,
  onOpen,
}: Props) {
  return (
    <div
      className={cn(
        "group relative rounded-lg overflow-hidden border bg-white transition-all cursor-pointer",
        selected
          ? "border-[var(--color-accent)] ring-2 ring-[var(--color-accent)]"
          : "border-[var(--color-border)] hover:border-[var(--color-border-strong)] hover:shadow-sm",
      )}
      onClick={() => {
        if (selectionMode) onToggleSelect();
        else onOpen();
      }}
    >
      <div className="aspect-square bg-[var(--color-bg-subtle)] overflow-hidden">
        {/* eslint-disable-next-line @next/next/no-img-element */}
        <img
          src={item.url}
          alt={item.name}
          loading="lazy"
          className="w-full h-full object-cover group-hover:scale-[1.02] transition-transform duration-300"
        />
      </div>

      {/* selection checkbox */}
      <button
        type="button"
        onClick={(e) => {
          e.stopPropagation();
          onToggleSelect();
        }}
        className={cn(
          "absolute top-2 left-2 size-5 rounded grid place-items-center border transition-all",
          selected
            ? "bg-[var(--color-accent)] border-[var(--color-accent)] text-white"
            : "bg-white/90 border-[var(--color-border-strong)] opacity-0 group-hover:opacity-100",
        )}
        aria-label={selected ? "Deselect" : "Select"}
      >
        {selected && <Check className="size-3" strokeWidth={3} />}
      </button>

      <div className="px-2.5 py-1.5 border-t border-[var(--color-border)]">
        <div className="text-xs font-medium truncate" title={item.name}>
          {item.name}
        </div>
        <div className="flex items-center justify-between text-[10px] text-[var(--color-text-subtle)] tabular-nums">
          <span className="truncate">{prettyCategory(item.category)}</span>
          <span>{formatBytes(item.size)}</span>
        </div>
      </div>
    </div>
  );
}
