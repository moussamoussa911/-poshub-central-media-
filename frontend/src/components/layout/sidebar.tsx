"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { useQuery } from "@tanstack/react-query";
import { listCategories } from "@/lib/api";
import { cn, prettyCategory } from "@/lib/utils";
import {
  Images,
  Upload,
  Settings,
  BarChart3,
  Users,
  Palette,
  FolderTree,
} from "lucide-react";

interface SidebarProps {
  activeCategory: string;
  onSelectCategory: (cat: string) => void;
  onClose?: () => void;
}

const NAV = [
  { href: "/", label: "Gallery", icon: Images },
  { href: "/upload", label: "Upload", icon: Upload },
];

const SETTINGS_NAV = [
  { href: "/settings/team", label: "Team", icon: Users },
  { href: "/settings/branding", label: "Branding", icon: Palette },
  { href: "/settings/categories", label: "Categories", icon: FolderTree },
  { href: "/settings/stats", label: "Stats", icon: BarChart3 },
];

export function Sidebar({ activeCategory, onSelectCategory, onClose }: SidebarProps) {
  const pathname = usePathname();
  const isGallery = pathname === "/";
  const { data } = useQuery({
    queryKey: ["categories"],
    queryFn: listCategories,
  });

  const cats = data?.items ?? [];

  return (
    <aside className="w-64 shrink-0 border-r border-[var(--color-border)] bg-[var(--color-bg-subtle)] flex flex-col h-screen sticky top-0">
      <div className="px-4 h-14 flex items-center border-b border-[var(--color-border)]">
        <Link href="/" className="font-semibold tracking-tight text-sm flex items-center gap-2">
          <span className="size-6 rounded-md bg-[var(--color-text)] text-white grid place-items-center text-xs">
            M
          </span>
          Media Center
        </Link>
      </div>

      <nav className="flex-1 overflow-y-auto px-2 py-3 space-y-4 text-sm">
        <div>
          {NAV.map((it) => {
            const Icon = it.icon;
            const active = pathname === it.href;
            return (
              <Link
                key={it.href}
                href={it.href}
                onClick={onClose}
                className={cn(
                  "flex items-center gap-2 px-2 py-1.5 rounded-md text-[var(--color-text-muted)] hover:bg-[var(--color-bg-hover)] hover:text-[var(--color-text)] transition-colors",
                  active && "bg-[var(--color-bg-hover)] text-[var(--color-text)] font-medium",
                )}
              >
                <Icon className="size-4" />
                {it.label}
              </Link>
            );
          })}
        </div>

        {isGallery && (
          <div>
            <div className="px-2 pb-1 text-[10px] font-medium uppercase tracking-widest text-[var(--color-text-subtle)]">
              Categories
            </div>
            <div className="space-y-0.5">
              {cats.map((c) => {
                const active = activeCategory === c.name;
                return (
                  <button
                    key={c.name}
                    onClick={() => {
                      onSelectCategory(c.name);
                      onClose?.();
                    }}
                    className={cn(
                      "w-full flex items-center justify-between gap-2 px-2 py-1.5 rounded-md text-left transition-colors",
                      active
                        ? "bg-[var(--color-bg-hover)] text-[var(--color-text)] font-medium"
                        : "text-[var(--color-text-muted)] hover:bg-[var(--color-bg-hover)] hover:text-[var(--color-text)]",
                    )}
                  >
                    <span className="truncate">{prettyCategory(c.name)}</span>
                    <span className="text-xs text-[var(--color-text-subtle)] tabular-nums">
                      {c.count}
                    </span>
                  </button>
                );
              })}
            </div>
          </div>
        )}

        <div>
          <div className="px-2 pb-1 text-[10px] font-medium uppercase tracking-widest text-[var(--color-text-subtle)]">
            Settings
          </div>
          {SETTINGS_NAV.map((it) => {
            const Icon = it.icon;
            const active = pathname?.startsWith(it.href);
            return (
              <Link
                key={it.href}
                href={it.href}
                onClick={onClose}
                className={cn(
                  "flex items-center gap-2 px-2 py-1.5 rounded-md text-[var(--color-text-muted)] hover:bg-[var(--color-bg-hover)] hover:text-[var(--color-text)] transition-colors",
                  active && "bg-[var(--color-bg-hover)] text-[var(--color-text)] font-medium",
                )}
              >
                <Icon className="size-4" />
                {it.label}
              </Link>
            );
          })}
        </div>
      </nav>

      <div className="border-t border-[var(--color-border)] p-2">
        <Link
          href="/settings"
          className="flex items-center gap-2 px-2 py-1.5 rounded-md text-xs text-[var(--color-text-muted)] hover:bg-[var(--color-bg-hover)]"
        >
          <Settings className="size-3.5" />
          Workspace
        </Link>
      </div>
    </aside>
  );
}
