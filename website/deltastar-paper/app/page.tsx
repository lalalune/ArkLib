import { Header } from "@/components/sections/Header";
import { Abstract } from "@/components/sections/Abstract";
import { PrizeBox } from "@/components/sections/PrizeBox";
import { Contributors } from "@/components/sections/Contributors";
import { Problem } from "@/components/sections/Problem";
import { Method } from "@/components/sections/Method";
import { Results } from "@/components/sections/Results";
import { Refutations } from "@/components/sections/Refutations";
import { OpenCore } from "@/components/sections/OpenCore";
import { Discussion } from "@/components/sections/Discussion";
import { Timeline } from "@/components/sections/Timeline";
import { References } from "@/components/sections/References";
import { DegenProvider } from "@/components/degen/DegenProvider";
import { EliPopup } from "@/components/degen/EliPopup";
import { Eli5 } from "@/components/degen/Eli5";

const toc = [
  { href: "#abstract", label: "Abstract" },
  { href: "#prize", label: "The prize" },
  { href: "#problem", label: "1 \u2002The problem" },
  { href: "#method", label: "2 \u2002Method" },
  { href: "#results", label: "3 \u2002Results" },
  { href: "#refutations", label: "4 \u2002Refutations" },
  { href: "#open-core", label: "5 \u2002The open core" },
  { href: "#discussion", label: "6 \u2002Discussion" },
  { href: "#timeline", label: "Timeline" },
  { href: "#contributors", label: "Contributors" },
  { href: "#references", label: "References" },
];

export default function Page() {
  return (
    <DegenProvider>
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
      <Eli5 k="abstract" />
      <Abstract />
      <PrizeBox />
      <Eli5 k="problem" />
      <Problem />
      <Eli5 k="method" />
      <Method />
      <Eli5 k="results" />
      <Results />
      <Eli5 k="refutations" />
      <Refutations />
      <Eli5 k="opencore" />
      <OpenCore />
      <Eli5 k="discussion" />
      <Discussion />
      <Timeline />
      <Contributors />
      <References />

      <footer className="prose-col mt-24 pt-8" style={{ borderTop: "1px solid var(--rule)" }}>
        <p className="text-[0.85rem]" style={{ color: "var(--ink-faint)" }}>
          The δ* campaign &middot;{" "}
          <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>{" "}
          &middot; every theorem on this page is verifiable by{" "}
          <code className="inline">#print axioms</code>. The prize problem
          remains open; this page is the map.
        </p>
      </footer>
    </main>
    <EliPopup />
    </DegenProvider>
  );
}
