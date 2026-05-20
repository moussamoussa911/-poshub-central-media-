"use client";

import { useState } from "react";
import { useMutation, useQuery, useQueryClient } from "@tanstack/react-query";
import {
  deleteUser,
  listUsers,
  upsertUser,
  type GalleryRole,
  type GalleryUser,
} from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { Plus, Trash2, Loader2, X } from "lucide-react";

interface DraftUser {
  username: string;
  display_name: string;
  role: GalleryRole;
  password: string;
  active: boolean;
}

const EMPTY_DRAFT: DraftUser = {
  username: "",
  display_name: "",
  role: "editor",
  password: "",
  active: true,
};

export default function TeamPage() {
  const qc = useQueryClient();
  const { data, isLoading } = useQuery({
    queryKey: ["users"],
    queryFn: listUsers,
  });
  const users = data?.items ?? [];

  const [draft, setDraft] = useState<DraftUser | null>(null);
  const [error, setError] = useState<string | null>(null);

  const upsertMut = useMutation({
    mutationFn: (d: DraftUser) =>
      upsertUser({
        username: d.username,
        display_name: d.display_name,
        role: d.role,
        password: d.password || undefined,
        active: d.active,
      }),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ["users"] });
      setDraft(null);
      setError(null);
    },
    onError: (e: Error) => setError(e.message),
  });

  const deleteMut = useMutation({
    mutationFn: (u: string) => deleteUser(u),
    onSuccess: () => qc.invalidateQueries({ queryKey: ["users"] }),
    onError: (e: Error) => setError(e.message),
  });

  function startEdit(u: GalleryUser) {
    setDraft({
      username: u.username,
      display_name: u.display_name,
      role: u.role,
      password: "",
      active: !!u.active,
    });
  }

  if (isLoading)
    return (
      <div className="text-sm text-[var(--color-text-muted)]">
        <Loader2 className="size-4 inline animate-spin mr-2" /> Loading…
      </div>
    );

  return (
    <div className="space-y-5">
      <div className="flex items-center justify-between">
        <div>
          <h2 className="text-sm font-medium">Team members</h2>
          <p className="text-xs text-[var(--color-text-muted)] mt-1">
            Admin can manage everything, editors can upload and organize images.
          </p>
        </div>
        <Button
          variant="primary"
          size="sm"
          onClick={() => setDraft({ ...EMPTY_DRAFT })}
        >
          <Plus className="size-4" /> Add member
        </Button>
      </div>

      <div className="rounded-lg border border-[var(--color-border)] bg-white overflow-hidden">
        {users.map((u) => (
          <div
            key={u.username}
            className="flex items-center gap-3 px-4 py-3 border-b last:border-b-0 border-[var(--color-border)]"
          >
            <span className="size-8 rounded-full bg-[var(--color-bg-hover)] grid place-items-center font-medium uppercase text-sm">
              {u.display_name?.[0] ?? u.username[0]}
            </span>
            <div className="flex-1 min-w-0">
              <div className="text-sm font-medium">
                {u.display_name || u.username}
              </div>
              <div className="text-xs text-[var(--color-text-subtle)]">
                {u.username} · {u.role}
                {!u.active && " · inactive"}
              </div>
            </div>
            <Button variant="ghost" size="sm" onClick={() => startEdit(u)}>
              Edit
            </Button>
            <Button
              variant="ghost"
              size="icon"
              onClick={() => {
                if (
                  confirm(`Delete user ${u.username}? They will lose access immediately.`)
                )
                  deleteMut.mutate(u.username);
              }}
            >
              <Trash2 className="size-4 text-[var(--color-danger)]" />
            </Button>
          </div>
        ))}
      </div>

      {error && (
        <div className="text-sm rounded-md border border-[var(--color-danger)] bg-[var(--color-danger-bg)] text-[var(--color-danger)] px-3 py-2">
          {error}
        </div>
      )}

      {draft && (
        <div
          className="fixed inset-0 bg-black/40 z-40 grid place-items-center p-4"
          onClick={() => setDraft(null)}
        >
          <div
            className="bg-white rounded-xl shadow-xl w-full max-w-md p-6"
            onClick={(e) => e.stopPropagation()}
          >
            <div className="flex items-center justify-between mb-4">
              <h3 className="font-semibold">
                {users.find((u) => u.username === draft.username)
                  ? `Edit ${draft.username}`
                  : "New team member"}
              </h3>
              <Button variant="ghost" size="icon" onClick={() => setDraft(null)}>
                <X className="size-4" />
              </Button>
            </div>
            <div className="space-y-4">
              <div>
                <label className="text-xs text-[var(--color-text-muted)]">
                  Username
                </label>
                <Input
                  value={draft.username}
                  onChange={(e) => setDraft({ ...draft, username: e.target.value })}
                  disabled={
                    !!users.find((u) => u.username === draft.username)
                  }
                  className="mt-1"
                />
              </div>
              <div>
                <label className="text-xs text-[var(--color-text-muted)]">
                  Display name
                </label>
                <Input
                  value={draft.display_name}
                  onChange={(e) => setDraft({ ...draft, display_name: e.target.value })}
                  className="mt-1"
                />
              </div>
              <div>
                <label className="text-xs text-[var(--color-text-muted)]">
                  Role
                </label>
                <select
                  value={draft.role}
                  onChange={(e) =>
                    setDraft({ ...draft, role: e.target.value as GalleryRole })
                  }
                  className="mt-1 h-9 w-full rounded-md border border-[var(--color-border)] bg-white px-3 text-sm"
                >
                  <option value="editor">Editor</option>
                  <option value="admin">Admin</option>
                </select>
              </div>
              <div>
                <label className="text-xs text-[var(--color-text-muted)]">
                  {users.find((u) => u.username === draft.username)
                    ? "New password (leave blank to keep)"
                    : "Password"}
                </label>
                <Input
                  type="password"
                  value={draft.password}
                  onChange={(e) => setDraft({ ...draft, password: e.target.value })}
                  className="mt-1"
                />
              </div>
              <label className="flex items-center gap-2 text-sm">
                <input
                  type="checkbox"
                  checked={draft.active}
                  onChange={(e) => setDraft({ ...draft, active: e.target.checked })}
                />
                Active
              </label>
            </div>
            <div className="mt-6 flex justify-end gap-2">
              <Button variant="ghost" size="md" onClick={() => setDraft(null)}>
                Cancel
              </Button>
              <Button
                variant="primary"
                size="md"
                onClick={() => upsertMut.mutate(draft)}
                disabled={upsertMut.isPending || !draft.username.trim()}
              >
                {upsertMut.isPending ? "Saving…" : "Save"}
              </Button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
