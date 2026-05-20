"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { AppShell } from "@/components/layout/app-shell";
import { cn } from "@/lib/utils";

const NAV = [
  { href: "/settings/team", label: "Team" },
  { href: "/settings/branding", label: "Branding" },
  { href: "/settings/categories", label: "Categories" },
  { href: "/settings/stats", label: "Stats" },
];

export default function SettingsLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  const pathname = usePathname();
  return (
    <AppShell>
      <div className="px-4 md:px-8 py-6 max-w-4xl mx-auto">
        <div className="text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
          Settings
        </div>
        <h1 className="mt-1 text-2xl font-semibold tracking-tight">Workspace</h1>

        <nav className="mt-6 flex gap-1 border-b border-[var(--color-border)] -mb-px overflow-x-auto">
          {NAV.map((it) => {
            const active = pathname === it.href;
            return (
              <Link
                key={it.href}
                href={it.href}
                className={cn(
                  "px-3 py-2 text-sm border-b-2 -mb-px transition-colors whitespace-nowrap",
                  active
                    ? "border-[var(--color-text)] text-[var(--color-text)] font-medium"
                    : "border-transparent text-[var(--color-text-muted)] hover:text-[var(--color-text)]",
                )}
              >
                {it.label}
              </Link>
            );
          })}
        </nav>

        <div className="mt-6">{children}</div>
      </div>
    </AppShell>
  );
}
