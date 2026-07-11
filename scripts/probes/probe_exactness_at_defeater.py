#!/usr/bin/env python3
"""probe_exactness_at_defeater.py — does interleaving EXACTNESS fail at the S2(b)
defeater configurations? (#357)

The MissingLine/ObstructionBound covering route is refuted at the Johnson radius
(MissingLineDefeater.lean): obstruction families overflow every <= q dominating
family. But the route is sufficient, not necessary. This probe computes the two
sides of [Jo26] Thm 4.2 EXACTLY at the defeater configs:

    epsMCAG(C, delta, G)        — base generator-MCA error (sup over l-row stacks)
    epsMCAG(C^(x)s, delta, G)   — interleaved (s = 2 columns)

for C = repetition code, n = 4, l = 2, G = identity on F^2 (all coefficient pairs),
at delta = 1/2 (Johnson, where the defeaters live) and delta = 1/4 (sub-Johnson
control). Fields F_2 (exhaustive: 2^8 base, 2^16 interleaved stacks) and F_3
(3^8 = 6561 base, 3^16 = 43M interleaved — reduced by per-word codeword-coset
canonicalization, verified exact for the event structure).

Outcomes:
  * interleaved > base  -> genuine exactness counterexample at Johnson (formalize!)
  * interleaved == base -> the hitting-number framing is provably non-tight;
                           exactness survives the covering route's death.

Written from the Lean definitions (mcaEventG / stackJointAgreesOn / ^(x)) with
tuple semantics; no shared code with the search probes.
"""

import itertools
import sys
from fractions import Fraction


def run(P, N, minT, reduce_cosets=False):
    print(f"\n=== F_{P}, n={N}, repetition code, l=2, s=2, |T|>={minT} "
          f"(delta = {Fraction(N - minT, N)}) ===")
    words = list(itertools.product(range(P), repeat=N))
    cws = [tuple([c] * N) for c in range(P)]
    masks = [T for r in range(minT, N + 1)
             for T in itertools.combinations(range(N), r)]
    seeds = list(itertools.product(range(P), repeat=2))

    def expl(w, T):
        return any(all(w[i] == c[i] for i in T) for c in cws)

    def comb(a, u, b, v):
        return tuple((a * ui + b * vi) % P for ui, vi in zip(u, v))

    # base words modulo codeword translation (event structure invariant)
    def rep(w):
        return min(tuple((wi + c) % P for wi in w) for c in range(P))

    base_words = sorted({rep(w) for w in words}) if reduce_cosets else words

    # --- base epsMCAG: stacks f = (f0, f1), badness of seed (a,b) ---
    def base_bad(f0, f1, ab):
        a, b = ab
        w = comb(a, f0, b, f1)
        for T in masks:
            if expl(w, T) and not (expl(f0, T) and expl(f1, T)):
                return True
        return False

    best_base, arg_base = 0, None
    for f0 in base_words:
        for f1 in base_words:
            cnt = sum(1 for ab in seeds if base_bad(f0, f1, ab))
            if cnt > best_base:
                best_base, arg_base = cnt, (f0, f1)
    eps_base = Fraction(best_base, len(seeds))
    print(f"base epsMCAG  = {best_base}/{len(seeds)} = {eps_base}  "
          f"(maximizer {arg_base})")

    # --- interleaved epsMCAG: stacks U with rows (x_j, y_j) ---
    def inter_bad(x0, y0, x1, y1, ab):
        a, b = ab
        c0 = comb(a, x0, b, x1)
        c1 = comb(a, y0, b, y1)
        for T in masks:
            if expl(c0, T) and expl(c1, T) and not (
                    expl(x0, T) and expl(y0, T) and expl(x1, T) and expl(y1, T)):
                return True
        return False

    best_int, arg_int = 0, None
    for x0 in base_words:
        for y0 in base_words:
            for x1 in base_words:
                for y1 in base_words:
                    cnt = sum(1 for ab in seeds if inter_bad(x0, y0, x1, y1, ab))
                    if cnt > best_int:
                        best_int, arg_int = cnt, (x0, y0, x1, y1)
    eps_int = Fraction(best_int, len(seeds))
    print(f"inter epsMCAG = {best_int}/{len(seeds)} = {eps_int}  "
          f"(maximizer {arg_int})")

    if eps_int > eps_base:
        print(">>> EXACTNESS FAILS: interleaved error strictly exceeds base — "
              "genuine [Jo26] Thm 4.4-style counterexample at this radius")
    elif eps_int == eps_base:
        print(">>> exactness HOLDS despite the covering route's death — "
              "the hitting-number framing is non-tight here")
    else:
        print(">>> impossible (interleaved < base) — check engines!")
    return eps_base, eps_int


def main():
    # F2 rungs: fully exhaustive, no reduction
    run(2, 4, 2)   # Johnson radius (the defeater config)
    run(2, 4, 3)   # sub-Johnson control
    # F3 rungs: coset-reduced (exact for the event structure)
    run(3, 4, 2, reduce_cosets=True)   # Johnson (the F3 defeater config)
    run(3, 4, 3, reduce_cosets=True)   # sub-Johnson control
    return 0


if __name__ == "__main__":
    sys.exit(main())
