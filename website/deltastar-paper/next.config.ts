import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  output: "export",
  // GitHub Pages serves this site under /deltastar/; Cloudflare Pages serves
  // it at the root. The workflow sets PAGES_BASE_PATH=/deltastar, local dev
  // and Cloudflare builds leave it unset.
  basePath: process.env.PAGES_BASE_PATH || "",
};

export default nextConfig;
