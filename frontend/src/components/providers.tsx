"use client";

import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { useState } from "react";
import { ApiError } from "@/lib/api";

export function Providers({ children }: { children: React.ReactNode }) {
  const [client] = useState(
    () =>
      new QueryClient({
        defaultOptions: {
          queries: {
            // Cache for 5 minutes — categories and lists rarely change.
            staleTime: 5 * 60_000,
            gcTime: 10 * 60_000,
            refetchOnWindowFocus: false,
            // Retry on 429 with exponential backoff; don't retry on 4xx
            // (besides 429) because they won't recover.
            retry: (failureCount, error) => {
              if (failureCount >= 4) return false;
              if (error instanceof ApiError) {
                if (error.status === 429) return true;
                if (error.status >= 400 && error.status < 500) return false;
              }
              return failureCount < 2;
            },
            retryDelay: (attempt) =>
              Math.min(30_000, 1000 * Math.pow(2, attempt)) + Math.random() * 500,
          },
          mutations: {
            retry: (failureCount, error) => {
              if (failureCount >= 2) return false;
              if (error instanceof ApiError && error.status === 429) return true;
              return false;
            },
            retryDelay: (attempt) => 1000 * Math.pow(2, attempt),
          },
        },
      }),
  );

  return <QueryClientProvider client={client}>{children}</QueryClientProvider>;
}
