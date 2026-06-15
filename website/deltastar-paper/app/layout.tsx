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
    "Pinning δ*: Machine-Checked Thresholds for Mutual Correlated Agreement of Smooth Reed–Solomon Codes",
  description:
    "A formal-verification study of the mutual correlated agreement threshold δ* for smooth-domain Reed–Solomon codes, conducted in Lean 4 over the ArkLib library. We prove a structural decoupling that isolates the field-dependent part of the threshold from the purely combinatorial part, give exact sub-Johnson pins and unconditional ceilings, and state the beyond-Johnson floor question as a single open combinatorial crossing. Each statement is labelled proven, computational, or open.",
  openGraph: {
    title:
      "Pinning δ*: Machine-Checked Thresholds for MCA of Smooth Reed–Solomon Codes",
    description:
      "A formal-verification study of the MCA threshold δ* for smooth Reed–Solomon codes in Lean 4 over ArkLib. A machine-checked decoupling reduces the beyond-Johnson floor to one open combinatorial crossing, with exact pins and impossibility results. Proven, computational, and open statements are labelled distinctly.",
    type: "article",
    siteName: "ArkLib δ* formalization",
  },
  twitter: {
    card: "summary_large_image",
    title:
      "Pinning δ*: Machine-Checked Thresholds for MCA of Smooth Reed–Solomon Codes",
    description:
      "A Lean 4 formal-verification study of the MCA threshold δ* for smooth Reed–Solomon codes. The decoupling reduces the beyond-Johnson floor to one open combinatorial crossing. Proven, computational, and open are labelled distinctly.",
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
