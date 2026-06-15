import { Header } from "@/components/sections/Header";
import { Abstract } from "@/components/sections/Abstract";
import { Contributors } from "@/components/sections/Contributors";
import { Problem } from "@/components/sections/Problem";
import { Method } from "@/components/sections/Method";
import { Results } from "@/components/sections/Results";
import { Refutations } from "@/components/sections/Refutations";
import { OpenCore } from "@/components/sections/OpenCore";
import { Discussion } from "@/components/sections/Discussion";
import { Timeline } from "@/components/sections/Timeline";
import { References } from "@/components/sections/References";

const toc = [
  { href: "#abstract", label: "Abstract" },
  { href: "#problem", label: "1 \u2002The threshold and the window" },
  { href: "#method", label: "2 \u2002Methodology" },
  { href: "#results", label: "3 \u2002The decoupling" },
  { href: "#refutations", label: "4 \u2002Refutations as results" },
  { href: "#open-core", label: "5 \u2002The floor reduces to a crossing" },
  { href: "#discussion", label: "6 \u2002Discussion" },
  { href: "#timeline", label: "Campaign timeline" },
  { href: "#contributors", label: "Contributors" },
  { href: "#references", label: "References" },
];

export default function Page() {
  return (
    <main className="px-5 md:px-8 pb-28">
      <nav className="toc-nav hidden 2xl:block" aria-label="Contents">
        <p
          className="sc-label font-semibold mb-2"
          style={{ color: "var(--ink-secondary)" }}
        >
          Contents
        </p>
        {toc.map((t) => (
          <a key={t.href} href={t.href}>
            {t.label}
          </a>
        ))}
      </nav>

      <Header />
      <Abstract />
      <Problem />
      <Method />
      <Results />
      <Refutations />
      <OpenCore />
      <Discussion />
      <Timeline />
      <Contributors />
      <References />

      <footer className="prose-col mt-24 pt-8" style={{ borderTop: "1px solid var(--rule)" }}>
        <p className="text-[0.85rem]" style={{ color: "var(--ink-faint)" }}>
          The ArkLib δ* formalization effort &middot;{" "}
          <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>{" "}
          &middot; every result labelled proven on this page is verifiable by{" "}
          <code className="inline">#print axioms</code>. The beyond-Johnson
          floor remains an open problem.
        </p>
      </footer>
    </main>
  );
}
