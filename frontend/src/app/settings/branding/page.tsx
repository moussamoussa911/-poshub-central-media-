"use client";

import { useEffect, useState } from "react";
import { useMutation, useQuery } from "@tanstack/react-query";
import { getBrand, setBrand, type Brand } from "@/lib/api";
import { Input } from "@/components/ui/input";
import { Button } from "@/components/ui/button";
import { Save, Loader2 } from "lucide-react";

export default function BrandingPage() {
  const { data, isLoading } = useQuery({
    queryKey: ["brand"],
    queryFn: getBrand,
  });

  const [form, setForm] = useState<Partial<Brand>>({});
  const [saved, setSaved] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    if (data?.brand) setForm(data.brand);
  }, [data]);

  const mut = useMutation({
    mutationFn: () => setBrand(form),
    onSuccess: () => {
      setSaved(true);
      setError(null);
      setTimeout(() => setSaved(false), 2000);
    },
    onError: (e: Error) => setError(e.message),
  });

  if (isLoading)
    return (
      <div className="text-sm text-[var(--color-text-muted)]">
        <Loader2 className="size-4 inline animate-spin mr-2" /> Loading…
      </div>
    );

  return (
    <div className="max-w-xl space-y-5">
      <div>
        <label className="text-xs text-[var(--color-text-muted)]">Company name</label>
        <Input
          value={form.company_name ?? ""}
          onChange={(e) => setForm((f) => ({ ...f, company_name: e.target.value }))}
          className="mt-1"
        />
      </div>
      <div>
        <label className="text-xs text-[var(--color-text-muted)]">Tagline</label>
        <Input
          value={form.tagline ?? ""}
          onChange={(e) => setForm((f) => ({ ...f, tagline: e.target.value }))}
          className="mt-1"
        />
      </div>
      <div>
        <label className="text-xs text-[var(--color-text-muted)]">Logo URL</label>
        <Input
          value={form.logo_url ?? ""}
          onChange={(e) => setForm((f) => ({ ...f, logo_url: e.target.value }))}
          placeholder="https://…/logo.png"
          className="mt-1"
        />
        {form.logo_url && (
          // eslint-disable-next-line @next/next/no-img-element
          <img
            src={form.logo_url}
            alt="logo preview"
            className="mt-2 size-16 object-contain rounded border border-[var(--color-border)] bg-white p-2"
          />
        )}
      </div>
      <div>
        <label className="text-xs text-[var(--color-text-muted)]">About text</label>
        <textarea
          value={form.about_text ?? ""}
          onChange={(e) => setForm((f) => ({ ...f, about_text: e.target.value }))}
          rows={4}
          className="mt-1 w-full rounded-md border border-[var(--color-border)] bg-white px-3 py-2 text-sm"
        />
      </div>

      {error && (
        <div className="text-sm rounded-md border border-[var(--color-danger)] bg-[var(--color-danger-bg)] text-[var(--color-danger)] px-3 py-2">
          {error}
        </div>
      )}

      <div className="flex items-center gap-2 pt-2">
        <Button
          variant="primary"
          size="md"
          onClick={() => mut.mutate()}
          disabled={mut.isPending}
        >
          {mut.isPending ? (
            <Loader2 className="size-4 animate-spin" />
          ) : (
            <Save className="size-4" />
          )}
          Save
        </Button>
        {saved && (
          <span className="text-sm text-[var(--color-success)]">Saved.</span>
        )}
      </div>
    </div>
  );
}
