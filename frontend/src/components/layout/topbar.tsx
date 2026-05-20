"use client";

import { useRouter } from "next/navigation";
import { logout, type GalleryUser } from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Menu, LogOut, Search } from "lucide-react";
import { Input } from "@/components/ui/input";

interface TopbarProps {
  user: GalleryUser | null;
  onMenuClick?: () => void;
  search?: string;
  onSearchChange?: (v: string) => void;
  searchPlaceholder?: string;
  children?: React.ReactNode;
}

export function Topbar({
  user,
  onMenuClick,
  search,
  onSearchChange,
  searchPlaceholder = "Search images…",
  children,
}: TopbarProps) {
  const router = useRouter();

  async function handleLogout() {
    await logout();
    router.replace("/login");
  }

  return (
    <header className="h-14 border-b border-[var(--color-border)] bg-[var(--color-bg)] sticky top-0 z-10 flex items-center px-3 md:px-6 gap-3">
      <Button
        variant="ghost"
        size="icon"
        onClick={onMenuClick}
        className="md:hidden"
        aria-label="Open menu"
      >
        <Menu className="size-4" />
      </Button>

      {onSearchChange && (
        <div className="flex-1 max-w-md relative">
          <Search className="size-4 absolute left-2.5 top-1/2 -translate-y-1/2 text-[var(--color-text-subtle)]" />
          <Input
            value={search ?? ""}
            onChange={(e) => onSearchChange(e.target.value)}
            placeholder={searchPlaceholder}
            className="pl-8"
          />
        </div>
      )}

      <div className="ml-auto flex items-center gap-3">
        {children}
        {user && (
          <div className="flex items-center gap-2 text-xs">
            <span className="size-7 rounded-full bg-[var(--color-bg-hover)] grid place-items-center font-medium uppercase">
              {user.display_name?.[0] ?? user.username[0]}
            </span>
            <div className="hidden md:block leading-tight">
              <div className="font-medium">
                {user.display_name || user.username}
              </div>
              <div className="text-[var(--color-text-subtle)] capitalize">
                {user.role}
              </div>
            </div>
          </div>
        )}
        <Button
          variant="ghost"
          size="icon"
          onClick={handleLogout}
          title="Sign out"
        >
          <LogOut className="size-4" />
        </Button>
      </div>
    </header>
  );
}
