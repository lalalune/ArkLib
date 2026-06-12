"use client";

import { useEffect, useRef, type ReactNode } from "react";
import { annotate } from "rough-notation";

type ScribbleType =
  | "underline"
  | "circle"
  | "box"
  | "highlight"
  | "strike-through"
  | "crossed-off"
  | "bracket";

/** Map semantic tones onto the paper's CSS custom properties. */
const TONE_VAR: Record<string, string> = {
  accent: "--accent",
  ink: "--ink-secondary",
  verified: "--verified",
  refuted: "--refuted",
  soft: "--accent-soft",
};

/**
 * Hand-drawn marginalia via rough-notation. Renders children in a span and
 * draws the annotation once, the first time the span scrolls into view.
 * Colors resolve from the design tokens at mount so dark mode stays correct.
 */
export function Scribble({
  type = "underline",
  tone = "accent",
  strokeWidth,
  padding,
  multiline = true,
  delay = 0,
  children,
}: {
  type?: ScribbleType;
  tone?: keyof typeof TONE_VAR;
  strokeWidth?: number;
  padding?: number;
  multiline?: boolean;
  delay?: number;
  children: ReactNode;
}) {
  const ref = useRef<HTMLSpanElement>(null);

  useEffect(() => {
    const el = ref.current;
    if (!el) return;
    if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) return;

    const cssVar = TONE_VAR[tone] ?? "--accent";
    const color =
      getComputedStyle(document.documentElement)
        .getPropertyValue(cssVar)
        .trim() || "#8a3033";

    const annotation = annotate(el, {
      type,
      color,
      strokeWidth: strokeWidth ?? (type === "highlight" ? 1 : 1.5),
      padding:
        padding ?? (type === "circle" ? 6 : type === "box" ? 4 : 2),
      multiline,
      iterations: 2,
      animationDuration: 800,
    });

    let timer: ReturnType<typeof setTimeout> | undefined;
    const io = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) {
          if (entry.isIntersecting) {
            timer = setTimeout(() => annotation.show(), delay);
            io.disconnect();
          }
        }
      },
      { threshold: 0.5, rootMargin: "0px 0px -8% 0px" },
    );
    io.observe(el);

    return () => {
      io.disconnect();
      if (timer) clearTimeout(timer);
      annotation.remove();
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  return <span ref={ref}>{children}</span>;
}
