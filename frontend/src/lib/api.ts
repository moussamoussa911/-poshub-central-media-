// Lightweight API client for the POS-Hub Media Center backend.
// Auth via `X-Gallery-Session` header (token from /gallery-admin/login),
// with optional fallback to `X-API-Key`.

export const API_BASE =
  process.env.NEXT_PUBLIC_API_BASE?.replace(/\/+$/, "") ??
  "https://poshub-central-media.onrender.com";

const TOKEN_KEY = "mc.session";
const APIKEY_KEY = "mc.apikey";
const USER_KEY = "mc.user";

export type GalleryRole = "admin" | "editor";

export interface GalleryUser {
  username: string;
  display_name: string;
  role: GalleryRole;
  active?: number;
  created_at?: string;
  updated_at?: string;
  last_login_at?: string;
}

export interface GalleryItem {
  name: string;
  category: string;
  rel_path: string;
  url: string;
  size: number;
  selected_count: number;
  downloaded_count: number;
}

export interface GalleryListResponse {
  ok: boolean;
  category: string;
  q: string;
  count: number;
  total: number;
  page: number;
  page_size: number;
  total_pages: number;
  items: GalleryItem[];
}

export interface CategoryItem {
  name: string;
  count: number;
  thumbnail_url: string;
  sort_order: number;
}

export interface Brand {
  company_name: string;
  tagline: string;
  logo_url: string;
  about_text: string;
  updated_at?: string;
}

class ApiError extends Error {
  status: number;
  body: unknown;
  constructor(message: string, status: number, body: unknown) {
    super(message);
    this.status = status;
    this.body = body;
  }
}

export function getToken(): string | null {
  if (typeof window === "undefined") return null;
  return window.localStorage.getItem(TOKEN_KEY);
}

export function getApiKey(): string | null {
  if (typeof window === "undefined") return null;
  return window.localStorage.getItem(APIKEY_KEY);
}

export function getUser(): GalleryUser | null {
  if (typeof window === "undefined") return null;
  const raw = window.localStorage.getItem(USER_KEY);
  if (!raw) return null;
  try {
    return JSON.parse(raw) as GalleryUser;
  } catch {
    return null;
  }
}

export function setSession(token: string, user: GalleryUser) {
  window.localStorage.setItem(TOKEN_KEY, token);
  window.localStorage.setItem(USER_KEY, JSON.stringify(user));
}

export function setApiKey(key: string) {
  window.localStorage.setItem(APIKEY_KEY, key);
}

export function clearSession() {
  window.localStorage.removeItem(TOKEN_KEY);
  window.localStorage.removeItem(USER_KEY);
  window.localStorage.removeItem(APIKEY_KEY);
}

function authHeaders(): Record<string, string> {
  const headers: Record<string, string> = {};
  const token = getToken();
  if (token) headers["X-Gallery-Session"] = token;
  const key = getApiKey();
  if (key) headers["X-API-Key"] = key;
  return headers;
}

async function handle<T>(res: Response): Promise<T> {
  if (res.status === 204) return undefined as T;
  let body: unknown;
  const text = await res.text();
  try {
    body = text ? JSON.parse(text) : null;
  } catch {
    body = text;
  }
  if (!res.ok) {
    const msg =
      (body && typeof body === "object" && (body as { detail?: string }).detail) ||
      `${res.status} ${res.statusText}`;
    throw new ApiError(String(msg), res.status, body);
  }
  return body as T;
}

async function api<T>(
  path: string,
  init: RequestInit = {},
): Promise<T> {
  const headers: Record<string, string> = {
    ...authHeaders(),
    ...((init.headers as Record<string, string>) || {}),
  };
  // Don't set Content-Type on FormData (browser sets boundary)
  if (init.body && !(init.body instanceof FormData) && !headers["Content-Type"]) {
    headers["Content-Type"] = "application/json";
  }
  const res = await fetch(`${API_BASE}${path}`, { ...init, headers });
  return handle<T>(res);
}

// ----- AUTH ------------------------------------------------------------------

export interface LoginResponse {
  ok: boolean;
  expires_at?: number;
  user?: GalleryUser;
  session_token?: string;
}

export async function loginWithPassword(
  username: string,
  password: string,
): Promise<LoginResponse> {
  const fd = new FormData();
  fd.set("username", username);
  fd.set("password", password);
  return api<LoginResponse>("/gallery-admin/login", {
    method: "POST",
    body: fd,
  });
}

export async function loginWithApiKey(apiKey: string): Promise<LoginResponse> {
  const fd = new FormData();
  fd.set("api_key", apiKey);
  return api<LoginResponse>("/gallery-admin/login", {
    method: "POST",
    body: fd,
  });
}

export async function logout(): Promise<void> {
  try {
    await api("/gallery-admin/logout", { method: "POST" });
  } catch {
    // ignore — we'll clear locally anyway
  }
  clearSession();
}

export async function fetchMe(): Promise<{
  ok: boolean;
  user?: GalleryUser;
}> {
  return api("/gallery-admin/me");
}

// ----- GALLERY ---------------------------------------------------------------

export async function listGallery(opts: {
  category?: string;
  q?: string;
  page?: number;
  pageSize?: number;
}): Promise<GalleryListResponse> {
  const params = new URLSearchParams();
  if (opts.category) params.set("category", opts.category);
  if (opts.q) params.set("q", opts.q);
  params.set("page", String(opts.page ?? 1));
  params.set("page_size", String(opts.pageSize ?? 60));
  return api<GalleryListResponse>(`/api/gallery/list?${params.toString()}`);
}

export async function listCategories(): Promise<{
  ok: boolean;
  count: number;
  items: CategoryItem[];
}> {
  return api("/api/gallery/categories");
}

export async function createCategory(name: string): Promise<{
  ok: boolean;
  name: string;
}> {
  const fd = new FormData();
  fd.set("name", name);
  return api("/api/gallery/categories", { method: "POST", body: fd });
}

export async function deleteCategory(
  name: string,
  moveTo: string = "all",
): Promise<{ ok: boolean; deleted: string; moved_to: string; moved_count: number }> {
  const params = new URLSearchParams({ name, move_to: moveTo });
  return api(`/api/gallery/categories?${params.toString()}`, { method: "DELETE" });
}

export async function setCategoryOrder(names: string[]): Promise<{
  ok: boolean;
  count: number;
}> {
  return api("/api/gallery/categories/order", {
    method: "POST",
    body: JSON.stringify({ names }),
  });
}

export async function uploadImage(
  file: File | Blob,
  category: string,
  filename?: string,
): Promise<{
  ok: boolean;
  filename: string;
  category: string;
  image_url: string;
  image_url_rel: string;
  duplicate?: boolean;
}> {
  const fd = new FormData();
  fd.append("file", file, filename ?? (file instanceof File ? file.name : "upload.png"));
  fd.append("category", category || "all");
  return api("/api/menu/upload_image", { method: "POST", body: fd });
}

export async function renameItem(
  relPath: string,
  newName: string,
): Promise<{ ok: boolean; rel_path: string; name: string }> {
  const fd = new FormData();
  fd.set("rel_path", relPath);
  fd.set("new_name", newName);
  return api("/api/gallery/rename", { method: "POST", body: fd });
}

export async function moveItem(
  relPath: string,
  newCategory: string,
): Promise<{ ok: boolean; rel_path: string }> {
  const fd = new FormData();
  fd.set("rel_path", relPath);
  fd.set("new_category", newCategory);
  return api("/api/gallery/move", { method: "POST", body: fd });
}

export async function replaceItem(
  relPath: string,
  file: File,
): Promise<{ ok: boolean; rel_path: string }> {
  const fd = new FormData();
  fd.set("rel_path", relPath);
  fd.append("file", file, file.name);
  return api("/api/gallery/replace", { method: "POST", body: fd });
}

export async function deleteItem(relPath: string): Promise<{ ok: boolean }> {
  const params = new URLSearchParams({ rel_path: relPath });
  return api(`/api/gallery/item?${params.toString()}`, { method: "DELETE" });
}

export async function deleteMany(relPaths: string[]): Promise<{
  ok: boolean;
  deleted: number;
  failed: number;
}> {
  return api("/api/gallery/delete_many", {
    method: "POST",
    body: JSON.stringify({ rel_paths: relPaths }),
  });
}

export async function moveMany(
  relPaths: string[],
  newCategory: string,
): Promise<{ ok: boolean; moved: number; failed: number; category: string }> {
  return api("/api/gallery/move_many", {
    method: "POST",
    body: JSON.stringify({ rel_paths: relPaths, new_category: newCategory }),
  });
}

// ----- BRAND -----------------------------------------------------------------

export async function getBrand(): Promise<{ ok: boolean; brand: Brand }> {
  return api("/api/gallery/brand");
}

export async function setBrand(brand: Partial<Brand>): Promise<{
  ok: boolean;
  brand: Brand;
}> {
  return api("/api/gallery/brand", {
    method: "PUT",
    body: JSON.stringify(brand),
  });
}

// ----- TEAM ------------------------------------------------------------------

export async function listUsers(): Promise<{
  ok: boolean;
  items: GalleryUser[];
}> {
  return api("/api/gallery/users");
}

export async function upsertUser(payload: {
  username: string;
  display_name?: string;
  role?: GalleryRole;
  password?: string;
  active?: boolean;
}): Promise<{ ok: boolean }> {
  return api("/api/gallery/users", {
    method: "POST",
    body: JSON.stringify(payload),
  });
}

export async function deleteUser(username: string): Promise<{ ok: boolean }> {
  return api(`/api/gallery/users/${encodeURIComponent(username)}`, {
    method: "DELETE",
  });
}

export { ApiError };
