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
  title: "The Million-Dollar Window",
  description:
    "What happened when a swarm of AI agents attacked one of Ethereum's hardest open math problems, with a proof checker as referee. A campaign report on the mutual correlated agreement threshold δ* for smooth Reed-Solomon codes: the first exact thresholds ever computed for any code, 28 machine-checked refutations, and an honest map of the $1M Proximity Prize window, which remains open.",
  openGraph: {
    title: "The Million-Dollar Window",
    description:
      "A swarm of AI agents attacked a 25-year-old math problem under a $1M Ethereum Foundation prize, with the Lean 4 kernel as referee. First exact thresholds ever computed for any code. 28 attack hypotheses refuted, each refutation a theorem. The window is still open. This page is the map.",
    type: "article",
    siteName: "The δ* campaign",
  },
  twitter: {
    card: "summary_large_image",
    title: "The Million-Dollar Window",
    description:
      "A swarm of AI agents attacked a 25-year-old math problem under a $1M Ethereum Foundation prize, with a proof checker as referee. The window is still open. This page is the map.",
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
