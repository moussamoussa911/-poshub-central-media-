"use client";

import { useEffect, useState } from "react";
import {
  GalleryUser,
  getToken,
  getUser,
  fetchMe,
  clearSession,
} from "./api";

export interface AuthState {
  ready: boolean;
  user: GalleryUser | null;
}

export function useAuth(): AuthState {
  const [state, setState] = useState<AuthState>({ ready: false, user: null });

  useEffect(() => {
    let cancelled = false;
    const cached = getUser();
    if (cached) {
      setState({ ready: true, user: cached });
      // background refresh
      fetchMe()
        .then((r) => {
          if (cancelled) return;
          if (r.ok && r.user) {
            setState({ ready: true, user: r.user });
          } else {
            clearSession();
            setState({ ready: true, user: null });
          }
        })
        .catch(() => {
          // network blip — keep cached
        });
      return;
    }
    const token = getToken();
    if (!token) {
      setState({ ready: true, user: null });
      return;
    }
    fetchMe()
      .then((r) => {
        if (cancelled) return;
        if (r.ok && r.user) {
          setState({ ready: true, user: r.user });
        } else {
          clearSession();
          setState({ ready: true, user: null });
        }
      })
      .catch(() => {
        if (cancelled) return;
        setState({ ready: true, user: null });
      });
    return () => {
      cancelled = true;
    };
  }, []);

  return state;
}
