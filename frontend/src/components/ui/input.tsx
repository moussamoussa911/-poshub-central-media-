"use client";

import { forwardRef, type InputHTMLAttributes } from "react";
import { cn } from "@/lib/utils";

export const Input = forwardRef<HTMLInputElement, InputHTMLAttributes<HTMLInputElement>>(
  ({ className, ...props }, ref) => (
    <input
      ref={ref}
      className={cn(
        "h-9 w-full rounded-md border border-[var(--color-border)] bg-white px-3 text-sm placeholder:text-[var(--color-text-subtle)] focus:border-[var(--color-text)] focus:outline-none focus:ring-0 transition-colors",
        className,
      )}
      {...props}
    />
  ),
);
Input.displayName = "Input";
