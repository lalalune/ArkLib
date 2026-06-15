import type { Metadata } from "next";
import { Space_Grotesk, IBM_Plex_Mono } from "next/font/google";
import "katex/dist/katex.min.css";
import "./globals.css";

const grotesk = Space_Grotesk({
  subsets: ["latin"],
  weight: ["400", "500", "600", "700"],
  variable: "--font-grotesk",
  display: "swap",
});

const mono = IBM_Plex_Mono({
  subsets: ["latin"],
  weight: ["400", "500"],
  variable: "--font-mono",
  display: "swap",
});

const title = "Truth Mining · formal verification, mined and re-checkable";
const description =
  "We point an agent fleet at a formal target with a cheap trustless verifier and ship a kernel-certified proof you can re-check with one command. We proved a 25-year-open coding-theory problem this way. Now we do it on commission: formal verification of ZK circuits and smart-contract invariants. A false truth does not typecheck.";

export const metadata: Metadata = {
  title,
  description,
  openGraph: {
    title,
    description,
    type: "website",
    siteName: "Truth Mining",
  },
  twitter: {
    card: "summary_large_image",
    title,
    description,
  },
};

export default function RootLayout({
  children,
}: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en" className={`${grotesk.variable} ${mono.variable}`}>
      <body>{children}</body>
    </html>
  );
}
