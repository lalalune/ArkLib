# δ* campaign paper site

A research-paper-style website presenting the results of the ArkLib δ*
campaign: the first exact machine-checked MCA thresholds for any code, the
universal staircase law, the Welch–Berlekamp pencil programme, 28
machine-checked refutations, and a precise statement of the open core. The
prize problem itself remains open; the site is the map, and says so.

Live preview: https://deltastar-paper.pages.dev

## Stack

- Next.js 15 (app router), static export (`output: "export"`)
- Tailwind CSS v4
- Server-side KaTeX (no client math runtime)
- `rough-notation` for the hand-drawn marginalia (scroll-into-view scribbles)
- Typography: STIX Two Text (serif body), IBM Plex Mono (Lean artifacts)

## Develop

```sh
npm install
npm run dev
```

## Build

```sh
npm run build   # static export to out/
```

The site is fully static. `PAGES_BASE_PATH` controls Next's `basePath`:
unset for root-hosted deploys (Cloudflare Pages, local dev), set to
`/deltastar` by the GitHub Pages workflow so the export works under
`<pages-url>/deltastar/`.

## Easter egg

There is a "degen mode" toggle that renders an ELI5 translation panel above
each section. Both registers state the same facts; neither claims the prize
problem is solved.
