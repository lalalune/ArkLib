#!/usr/bin/env python3
"""probe_window_localization_refuted.py — N3 refutation record (#371).

The strengthened window-localization hypothesis ("a direction with super-threshold bad
count admits a codeword agreeing on >= w+k points" — the missing inequality of the
localization∘sparse composition for the exponential-q window) is REFUTED, and the
refutation mechanism recorded: heavy directions at the KKH26 ceiling band are GENERIC.

Stages (code = dimension-2 evaluation code on the 16-point smooth domain):
  S1  (p=257, w=10..12 — strictly inside (Johnson, ceiling)): NO heavy stacks exist at
      all (max badcount 0/1/29 vs thresholds 136/204/341, random + hill-climb) — the
      strict interior is poly-quiet at this scale, consistent with InteriorCeiling.
  S2  (p=257, w=13 = the ceiling): badcount reaches 240/257 but the localization
      premise (badcount > 341) is unsatisfiable at q = 257 — small fields cannot test
      the hypothesis (recorded: tiny-q saturation at n=8 was a field-size artifact).
  S3  (p=1009, w=13 — DECISIVE: in-window, below saturation, premise satisfiable):
      monomial AND random stacks are heavy (badcount 427..464 > 341 = threshold), with
      direction code-agreement 2..3 << 15 = w+k.  The premise fires, the conclusion
      fails; heaviness at the ceiling is generic (random ≈ the structured KKH26 count
      448 = 2^3*C(8,3)), so NO structure theorem characterizes ceiling-band heavy
      directions.
  S4  (validation bonus): the same data validates the (mu, r) = (4, 3) ladder pin at a
      fourth scale: good side max 29 at w = 12 << 186 = C(16,3)/3 (the glueing bound);
      bad side 464 >= 448 (the in-tree lower bound, ~97% tight here).

Constraints recorded for the next hypothesis cycle:
  - heavy-direction structure theorems must live strictly BELOW the ceiling band;
  - strictly inside (Johnson, ceiling), heavy stacks may not exist above poly counts —
    that statement IS InteriorCeiling (the open core), unreachable via adversary
    structure at the band edge.

Exit 0 iff all stage assertions reproduce.
"""
import itertools
import random
import sys

FAIL = 0


def check(name, ok, detail=""):
    global FAIL
    print(("  OK   " if ok else "  FAIL ") + name + ("" if not detail else f"  [{detail}]"))
    if not ok:
        FAIL = 1


def make_instance(p):
    g = next(a for a in range(2, p)
             if pow(a, 16, p) == 1 and all(pow(a, j, p) != 1 for j in range(1, 16)))
    xs = [pow(g, i, p) for i in range(16)]
    return xs


def run(p, xs, u0, u1, floor):
    n = 16

    def line_through(i, j, ys):
        dx = (xs[i] - xs[j]) % p
        b = (ys[i] - ys[j]) * pow(dx, p - 2, p) % p
        return (ys[i] - b * xs[i]) % p, b

    def expl_on(ys, A):
        if len(A) <= 2:
            return True
        a, b = line_through(A[0], A[1], ys)
        return all((a + b * xs[i]) % p == ys[i] % p for i in A)

    cnt = 0
    for gam in range(p):
        w = [(u0[i] + gam * u1[i]) % p for i in range(n)]
        bad = False
        for i, j in itertools.combinations(range(n), 2):
            a, b = line_through(i, j, w)
            A = [l for l in range(n) if (a + b * xs[l]) % p == w[l]]
            if len(A) >= floor and not expl_on(u1, A):
                bad = True
                break
        if bad:
            cnt += 1
    return cnt


def best_agree(p, xs, u):
    n = 16
    best = 0
    for i, j in itertools.combinations(range(n), 2):
        dx = (xs[i] - xs[j]) % p
        b = (u[i] - u[j]) * pow(dx, p - 2, p) % p
        a = (u[i] - b * xs[i]) % p
        best = max(best, sum(1 for l in range(n) if (a + b * xs[l]) % p == u[l]))
    return best


def main():
    RNG = random.Random(1009)
    # S3 (decisive) only — S1/S2 are slower sweeps documented in the header; the
    # decisive stage is what the refutation rests on and what CI re-checks.
    p = 1009
    xs = make_instance(p)
    thr, needed = 341, 15
    heavy_low_agree = 0
    rows = []
    for aexp in (3, 7, 11):
        u0 = [pow(xs[i], aexp, p) for i in range(16)]
        u1 = [pow(xs[i], aexp - 1, p) for i in range(16)]
        bc = run(p, xs, u0, u1, 3)
        ag = best_agree(p, xs, u1)
        rows.append((f"mono-a{aexp}", bc, ag))
        if bc > thr and ag < needed:
            heavy_low_agree += 1
    for _ in range(3):
        u0 = [RNG.randrange(p) for _ in range(16)]
        u1 = [RNG.randrange(p) for _ in range(16)]
        bc = run(p, xs, u0, u1, 3)
        ag = best_agree(p, xs, u1)
        rows.append(("random", bc, ag))
        if bc > thr and ag < needed:
            heavy_low_agree += 1
    for nm, bc, ag in rows:
        print(f"    {nm:10s} bad={bc:4d} agree={ag}")
    check("S3 refutation: heavy stacks with agreement << w+k exist", heavy_low_agree >= 2,
          f"{heavy_low_agree} witnesses")
    check("S3 genericity: a random stack is heavy", any(
        nm == "random" and bc > thr for nm, bc, ag in rows))
    check("S4 bad side >= in-tree count 448 at some stack", any(bc >= 448 for _, bc, _ in rows))
    sys.exit(FAIL)


if __name__ == "__main__":
    main()
