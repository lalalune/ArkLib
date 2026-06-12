import type { Metadata } from "next";
import { STIX_Two_Text, IBM_Plex_Mono } from "next/font/google";
import "katex/dist/katex.min.css";
import "./globals.css";

const serif = STIX_Two_Text({
  subsets: ["latin"],
  weight: ["400", "500", "600", "700"],
  style: ["normal", "italic"],
  variable: "--font-serif",
  display: "swap",
});

const mono = IBM_Plex_Mono({
  subsets: ["latin"],
  weight: ["400", "500"],
  variable: "--font-mono",
  display: "swap",
});

export const metadata: Metadata = {
  title:
    "Pinning δ*: Machine-Checked Thresholds for Mutual Correlated Agreement",
  description:
    "An agent-fleet campaign in Lean 4 produced the first exact mutual correlated agreement thresholds for any code, a universal staircase law for smooth Reed-Solomon codes, and an honest, kernel-checked map of the open core of the Ethereum Foundation Proximity Prize problem.",
  openGraph: {
    title: "Pinning δ*: Machine-Checked Thresholds for Mutual Correlated Agreement",
    description:
      "First exact MCA thresholds for any code, the universal staircase law, and an honest map of the open window — hundreds of axiom-clean Lean 4 theorems from an LLM agent fleet.",
    type: "article",
  },
};

export default function RootLayout({
  children,
}: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en" className={`${serif.variable} ${mono.variable}`}>
      <body style={{ fontFamily: "var(--font-serif), Georgia, serif" }}>
        {children}
      </body>
    </html>
  );
}
