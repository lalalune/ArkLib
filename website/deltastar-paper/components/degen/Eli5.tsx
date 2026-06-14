"use client";

import { useDegen } from "./DegenProvider";

const COPY: Record<string, string> = {
  abstract:
    "ok so basically: ethereum pays $1M to anyone who can pin down exactly how far you can push the error-checking trick inside zk proofs before it breaks. humans have been stuck on the hard part for 25 years. we pointed a robot army with a proof-checker at it and published every brick, win or fail.",
  problem:
    "there's a magic number called δ*. below it, the proof system is safe. above it, it breaks. everyone KNOWS roughly where it is (somewhere in a window between two lines mathematicians drew decades ago), but nobody can prove exactly where. that window is the entire $1M question.",
  "problem-window":
    "why 25 years? because proving anything past the 'Johnson radius' line turns out to be the same problem as a famous list-decoding question that's been open since the late 90s. it's not that nobody tried. it's that every road leads to the same wall.",
  method:
    "the loop: agents guess an attack, test it on tiny examples first (cheap), and only claim things a proof-checker (Lean) actually verifies. no trust-me-bro. a fake proof literally does not compile. failed ideas get written down as theorems too, so no agent wastes compute on a dead end twice.",
  "method-honesty":
    "the three rules: (1) no fake axioms, no placeholder 'trust me' theorems, ever. (2) every claim ships with a receipt the kernel checked. (3) if your idea dies, you publish the corpse. that last one is the secret weapon — the map of dead ends is half the value.",
  "method-probe":
    "before formalizing anything, run it on baby-sized codes in python. if the idea is wrong, a 30-second probe kills it for free. if it survives, THEN spend hours proving it in Lean. cheap filters first, expensive certainty second. this is why the fleet doesn't burn compute on vibes.",
  results:
    "the robot army computed the EXACT magic number for small codes — first time anyone has done that for ANY code, ever. plus laws for how the number moves, exact pins beyond the famous Johnson line on special slices, and a new pencil trick that crushed everything below the unique-decoding line down to one remaining question.",
  "results-pins":
    "this table is the flex. before this campaign, the number of codes (any kind, anywhere, by anyone) whose exact MCA threshold was known: zero. now there's a list. small codes, sure — but 'first ever' is 'first ever'.",
  "results-staircase":
    "turns out δ* doesn't slide smoothly, it climbs stairs. each step is exactly 1/n tall and the law for where the steps are is now a theorem — proven at the actual 2⁻¹²⁸ security budget the prize asks about, not a toy version of it.",
  "results-wb":
    "the new trick of the campaign: treat the decoding question as a 'pencil' of matrices (a line of them, one per scalar). old-school linear algebra, never aimed at this problem before. it ate the entire below-unique-decoding regime in one night and left exactly one named question standing.",
  "results-ownership":
    "the unification: two totally different attack lanes (the pencil trick and the dimension ladder) turned out to be the same theorem wearing different clothes. now the whole open problem compresses to one counting question: how many 'witness tuples' must each bad scalar own?",
  refutations:
    "every one of these boxes is an idea that LOOKED like it could win the $1M and got executed in public. that's not failure, that's the map. each corpse is a checked theorem saying 'this road is closed', so nobody walks it again.",
  opencore:
    "the actual $1M question? still open. anyone who tells you otherwise is larping. but it's been cornered into four equivalent forms, and we know exactly which wall you have to break (it's equivalent to a 25-year-old list-decoding problem). we mapped the wall and carved our initials into it.",
  "opencore-faces":
    "four doors, one room: crack ANY of these — list decoding past Johnson, character sums below √q, a monster bad-stack family, or the line-vs-ball incidence question — and δ* falls. they're proven equivalent. pick your poison.",
  discussion:
    "the point: when a proof-checker is the referee, math research becomes something you can SCALE with compute instead of waiting for one genius. the swarm doesn't sleep, doesn't bluff, and every claim is receipts. now extrapolate that to everything else humans are stuck on.",
};

export function Eli5({ k }: { k: string }) {
  const { degen } = useDegen();
  if (!degen) return null;
  const text = COPY[k];
  if (!text) return null;
  return (
    <div className="prose-col">
      <div
        className="mt-6 mb-2 rounded-md border-l-4 px-5 py-4 font-mono text-[0.88rem] leading-relaxed"
        style={{
          borderLeftColor: "var(--accent)",
          background: "var(--accent-soft)",
          color: "var(--ink)",
          transform: "rotate(-0.35deg)",
        }}
      >
        <span
          className="mr-2 font-semibold uppercase tracking-wider text-[0.7rem]"
          style={{ color: "var(--accent)" }}
        >
          degen translation
        </span>
        {text}
      </div>
    </div>
  );
}
