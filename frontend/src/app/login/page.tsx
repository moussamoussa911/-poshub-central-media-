"use client";

import { useRouter } from "next/navigation";
import { useEffect, useState } from "react";
import {
  ApiError,
  getToken,
  loginWithApiKey,
  loginWithPassword,
  setApiKey,
  setSession,
} from "@/lib/api";
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";
import { KeyRound, LogIn } from "lucide-react";

type Mode = "password" | "apikey";

export default function LoginPage() {
  const router = useRouter();
  const [mode, setMode] = useState<Mode>("password");
  const [username, setUsername] = useState("");
  const [password, setPassword] = useState("");
  const [apiKey, setApiKeyValue] = useState("");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    // already logged in?
    if (getToken()) router.replace("/");
  }, [router]);

  async function handleSubmit(e: React.FormEvent) {
    e.preventDefault();
    setError(null);
    setLoading(true);
    try {
      const resp =
        mode === "password"
          ? await loginWithPassword(username.trim(), password)
          : await loginWithApiKey(apiKey.trim());
      if (!resp.ok || !resp.session_token || !resp.user) {
        throw new Error("Login failed: invalid response from server.");
      }
      setSession(resp.session_token, resp.user);
      if (mode === "apikey") setApiKey(apiKey.trim());
      router.replace("/");
    } catch (err) {
      if (err instanceof ApiError) {
        setError(
          err.status === 401
            ? "Invalid credentials."
            : `Login failed (HTTP ${err.status}).`,
        );
      } else {
        setError(
          err instanceof Error ? err.message : "Network error. Please try again.",
        );
      }
    } finally {
      setLoading(false);
    }
  }

  return (
    <main className="min-h-screen grid grid-cols-1 md:grid-cols-2">
      <section className="hidden md:flex flex-col justify-between bg-[var(--color-bg-subtle)] border-r border-[var(--color-border)] p-10">
        <div>
          <div className="font-mono text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
            Media Center
          </div>
          <div className="mt-1 font-semibold tracking-tight">POS Hub</div>
        </div>
        <div className="max-w-md">
          <h1 className="text-3xl font-semibold tracking-tight leading-tight">
            Your team&apos;s shared image library.
          </h1>
          <p className="mt-3 text-[var(--color-text-muted)] text-sm leading-relaxed">
            Upload, organize and serve menu images across every branch and POS
            client. Sign in with your team account or recover access with your
            API key.
          </p>
        </div>
        <div className="text-xs text-[var(--color-text-subtle)]">
          v2 · Notion-style admin
        </div>
      </section>

      <section className="flex items-center justify-center p-8">
        <div className="w-full max-w-sm">
          <div className="text-xs uppercase tracking-widest text-[var(--color-text-muted)]">
            01 — Sign in
          </div>
          <h2 className="mt-1 text-2xl font-semibold tracking-tight">
            Welcome back.
          </h2>

          <div className="mt-6 flex gap-1 rounded-md border border-[var(--color-border)] p-1 bg-white">
            <button
              type="button"
              onClick={() => setMode("password")}
              className={`flex-1 text-xs h-7 rounded ${mode === "password" ? "bg-[var(--color-bg-hover)] font-medium" : "text-[var(--color-text-muted)]"}`}
            >
              Password
            </button>
            <button
              type="button"
              onClick={() => setMode("apikey")}
              className={`flex-1 text-xs h-7 rounded ${mode === "apikey" ? "bg-[var(--color-bg-hover)] font-medium" : "text-[var(--color-text-muted)]"}`}
            >
              API key
            </button>
          </div>

          <form onSubmit={handleSubmit} className="mt-6 space-y-4">
            {mode === "password" ? (
              <>
                <div>
                  <label className="text-xs text-[var(--color-text-muted)]">
                    Username
                  </label>
                  <Input
                    value={username}
                    onChange={(e) => setUsername(e.target.value)}
                    autoComplete="username"
                    required
                    autoFocus
                    className="mt-1"
                  />
                </div>
                <div>
                  <label className="text-xs text-[var(--color-text-muted)]">
                    Password
                  </label>
                  <Input
                    type="password"
                    value={password}
                    onChange={(e) => setPassword(e.target.value)}
                    autoComplete="current-password"
                    required
                    className="mt-1"
                  />
                </div>
              </>
            ) : (
              <div>
                <label className="text-xs text-[var(--color-text-muted)]">
                  API key
                </label>
                <Input
                  type="password"
                  value={apiKey}
                  onChange={(e) => setApiKeyValue(e.target.value)}
                  placeholder="pk_live_…"
                  required
                  autoFocus
                  className="mt-1 font-mono"
                />
                <p className="mt-2 text-xs text-[var(--color-text-subtle)]">
                  Found in your Render environment as{" "}
                  <code>POS_HUB_API_KEY</code>.
                </p>
              </div>
            )}

            {error && (
              <div className="text-sm rounded-md border border-[var(--color-danger)] bg-[var(--color-danger-bg)] text-[var(--color-danger)] px-3 py-2">
                {error}
              </div>
            )}

            <Button
              type="submit"
              variant="primary"
              size="lg"
              disabled={loading}
              className="w-full"
            >
              {mode === "password" ? (
                <LogIn className="size-4" />
              ) : (
                <KeyRound className="size-4" />
              )}
              {loading ? "Signing in…" : "Sign in"}
            </Button>
          </form>

          <p className="mt-6 text-xs text-[var(--color-text-subtle)]">
            Trouble signing in? Ask an admin to reset your password.
          </p>
        </div>
      </section>
    </main>
  );
}
