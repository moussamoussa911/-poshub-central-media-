"use client";

import { useMutation, useQueryClient } from "@tanstack/react-query";
import { deleteMany, moveMany, type CategoryItem } from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Trash2, FolderInput, X } from "lucide-react";
import { useState } from "react";

interface Props {
  selected: string[];
  categories: CategoryItem[];
  onClear: () => void;
}

export function BulkBar({ selected, categories, onClear }: Props) {
  const qc = useQueryClient();
  const [moveTo, setMoveTo] = useState("");
  const [error, setError] = useState<string | null>(null);

  const moveMut = useMutation({
    mutationFn: () => moveMany(selected, moveTo),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ["gallery"] });
      qc.invalidateQueries({ queryKey: ["categories"] });
      onClear();
      setMoveTo("");
    },
    onError: (e: Error) => setError(e.message),
  });

  const deleteMut = useMutation({
    mutationFn: () => deleteMany(selected),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ["gallery"] });
      qc.invalidateQueries({ queryKey: ["categories"] });
      onClear();
    },
    onError: (e: Error) => setError(e.message),
  });

  if (selected.length === 0) return null;

  return (
    <div className="fixed bottom-6 left-1/2 -translate-x-1/2 z-30">
      <div className="bg-[var(--color-text)] text-white shadow-xl rounded-xl px-4 py-3 flex items-center gap-3 text-sm">
        <span className="font-medium tabular-nums">
          {selected.length} selected
        </span>
        <div className="h-5 w-px bg-white/20" />

        <div className="flex items-center gap-1.5">
          <select
            value={moveTo}
            onChange={(e) => setMoveTo(e.target.value)}
            className="h-8 rounded-md bg-white/10 border border-white/20 px-2 text-xs text-white"
          >
            <option value="" disabled className="text-black">
              Move to…
            </option>
            {categories
              .filter((c) => c.name !== "all" || true)
              .map((c) => (
                <option key={c.name} value={c.name} className="text-black">
                  {c.name}
                </option>
              ))}
          </select>
          <Button
            size="sm"
            variant="secondary"
            disabled={!moveTo || moveMut.isPending}
            onClick={() => moveMut.mutate()}
            className="bg-white text-[var(--color-text)] hover:bg-white/90"
          >
            <FolderInput className="size-3.5" />
            Move
          </Button>
        </div>

        <Button
          size="sm"
          variant="danger"
          onClick={() => {
            if (
              confirm(
                `Delete ${selected.length} image${selected.length === 1 ? "" : "s"}? This cannot be undone.`,
              )
            )
              deleteMut.mutate();
          }}
          disabled={deleteMut.isPending}
        >
          <Trash2 className="size-3.5" />
          Delete
        </Button>

        <button
          onClick={onClear}
          className="ml-1 size-7 grid place-items-center rounded-md hover:bg-white/10"
          aria-label="Clear selection"
        >
          <X className="size-4" />
        </button>
      </div>

      {error && (
        <div className="mt-2 text-xs bg-red-600 text-white rounded-md px-3 py-2">
          {error}
        </div>
      )}
    </div>
  );
}
