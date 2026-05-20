"use client";

import { useRouter } from "next/navigation";
import { useEffect, useState } from "react";
import { useAuth } from "@/lib/auth";
import { Sidebar } from "./sidebar";
import { Topbar } from "./topbar";

interface AppShellProps {
  children: React.ReactNode;
  activeCategory?: string;
  onSelectCategory?: (cat: string) => void;
  search?: string;
  onSearchChange?: (v: string) => void;
  searchPlaceholder?: string;
  topbarExtras?: React.ReactNode;
}

export function AppShell({
  children,
  activeCategory = "all",
  onSelectCategory = () => {},
  search,
  onSearchChange,
  searchPlaceholder,
  topbarExtras,
}: AppShellProps) {
  const router = useRouter();
  const { ready, user } = useAuth();
  const [mobileOpen, setMobileOpen] = useState(false);

  useEffect(() => {
    if (ready && !user) {
      router.replace("/login");
    }
  }, [ready, user, router]);

  if (!ready) {
    return (
      <div className="min-h-screen grid place-items-center text-[var(--color-text-muted)] text-sm">
        Loading…
      </div>
    );
  }

  if (!user) return null;

  return (
    <div className="min-h-screen flex">
      {/* Desktop sidebar */}
      <div className="hidden md:block">
        <Sidebar
          activeCategory={activeCategory}
          onSelectCategory={onSelectCategory}
        />
      </div>

      {/* Mobile sidebar drawer */}
      {mobileOpen && (
        <div className="md:hidden fixed inset-0 z-20 flex">
          <div
            className="absolute inset-0 bg-black/30"
            onClick={() => setMobileOpen(false)}
          />
          <div className="relative">
            <Sidebar
              activeCategory={activeCategory}
              onSelectCategory={onSelectCategory}
              onClose={() => setMobileOpen(false)}
            />
          </div>
        </div>
      )}

      <div className="flex-1 min-w-0 flex flex-col">
        <Topbar
          user={user}
          onMenuClick={() => setMobileOpen(true)}
          search={search}
          onSearchChange={onSearchChange}
          searchPlaceholder={searchPlaceholder}
        >
          {topbarExtras}
        </Topbar>
        <main className="flex-1 min-w-0">{children}</main>
      </div>
    </div>
  );
}
