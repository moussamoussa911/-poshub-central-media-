"use client";

import { useState } from "react";
import { useMutation, useQuery, useQueryClient } from "@tanstack/react-query";
import {
  createCategory,
  deleteCategory,
  listCategories,
  setCategoryOrder,
} from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { ArrowDown, ArrowUp, Plus, Trash2, Loader2 } from "lucide-react";
import { prettyCategory } from "@/lib/utils";

export default function CategoriesPage() {
  const qc = useQueryClient();
  const { data, isLoading } = useQuery({
    queryKey: ["categories"],
    queryFn: listCategories,
  });
  const items = data?.items ?? [];

  const [newName, setNewName] = useState("");

  const createMut = useMutation({
    mutationFn: () => createCategory(newName.trim()),
    onSuccess: () => {
      setNewName("");
      qc.invalidateQueries({ queryKey: ["categories"] });
    },
  });

  const deleteMut = useMutation({
    mutationFn: (name: string) => deleteCategory(name, "all"),
    onSuccess: () => qc.invalidateQueries({ queryKey: ["categories"] }),
  });

  const orderMut = useMutation({
    mutationFn: (names: string[]) => setCategoryOrder(names),
    onSuccess: () => qc.invalidateQueries({ queryKey: ["categories"] }),
  });

  function move(idx: number, dir: -1 | 1) {
    const real = items.filter((c) => c.name !== "all");
    const j = idx + dir;
    if (j < 0 || j >= real.length) return;
    const next = real.slice();
    [next[idx], next[j]] = [next[j], next[idx]];
    orderMut.mutate(next.map((c) => c.name));
  }

  if (isLoading)
    return (
      <div className="text-sm text-[var(--color-text-muted)]">
        <Loader2 className="size-4 inline animate-spin mr-2" /> Loading…
      </div>
    );

  const real = items.filter((c) => c.name !== "all");

  return (
    <div className="space-y-6">
      <section>
        <h2 className="text-sm font-medium">Add category</h2>
        <p className="text-xs text-[var(--color-text-muted)] mt-1">
          Lowercase letters, numbers, dash and underscore only.
        </p>
        <form
          onSubmit={(e) => {
            e.preventDefault();
            if (newName.trim()) createMut.mutate();
          }}
          className="mt-2 flex gap-2"
        >
          <Input
            value={newName}
            onChange={(e) => setNewName(e.target.value)}
            placeholder="e.g. shisha"
            className="max-w-xs"
          />
          <Button
            type="submit"
            variant="primary"
            size="md"
            disabled={createMut.isPending || !newName.trim()}
          >
            <Plus className="size-4" />
            Add
          </Button>
        </form>
      </section>

      <section>
        <h2 className="text-sm font-medium">Order & manage</h2>
        <p className="text-xs text-[var(--color-text-muted)] mt-1">
          Drag-free reordering. Deleting moves its images to <code>all</code>.
        </p>

        <div className="mt-3 rounded-lg border border-[var(--color-border)] bg-white overflow-hidden">
          {real.length === 0 && (
            <div className="p-4 text-sm text-[var(--color-text-muted)]">
              No categories yet.
            </div>
          )}
          {real.map((c, i) => (
            <div
              key={c.name}
              className="flex items-center gap-3 px-3 py-2 border-b last:border-b-0 border-[var(--color-border)]"
            >
              {c.thumbnail_url ? (
                // eslint-disable-next-line @next/next/no-img-element
                <img
                  src={c.thumbnail_url}
                  alt=""
                  className="size-10 rounded object-cover bg-[var(--color-bg-subtle)]"
                />
              ) : (
                <div className="size-10 rounded bg-[var(--color-bg-subtle)]" />
              )}
              <div className="flex-1 min-w-0">
                <div className="text-sm font-medium">{prettyCategory(c.name)}</div>
                <div className="text-xs text-[var(--color-text-subtle)] tabular-nums">
                  {c.count} images · sort {c.sort_order}
                </div>
              </div>
              <div className="flex items-center gap-1">
                <Button
                  variant="ghost"
                  size="icon"
                  disabled={i === 0 || orderMut.isPending}
                  onClick={() => move(i, -1)}
                >
                  <ArrowUp className="size-4" />
                </Button>
                <Button
                  variant="ghost"
                  size="icon"
                  disabled={i === real.length - 1 || orderMut.isPending}
                  onClick={() => move(i, 1)}
                >
                  <ArrowDown className="size-4" />
                </Button>
                <Button
                  variant="ghost"
                  size="icon"
                  onClick={() => {
                    if (
                      confirm(
                        `Delete category "${c.name}"? Its ${c.count} images move to "all".`,
                      )
                    )
                      deleteMut.mutate(c.name);
                  }}
                  disabled={deleteMut.isPending}
                >
                  <Trash2 className="size-4 text-[var(--color-danger)]" />
                </Button>
              </div>
            </div>
          ))}
        </div>
      </section>
    </div>
  );
}
