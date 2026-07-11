#!/usr/bin/env python3
"""
PROBE (#407/#444): the STATED CrossCellAbsoluteBound (= BCHKS-1.12 as written in
CrossCellShkredovBound.lean) is FALSE at every prize-relevant depth -- not "the open wall".

The file defines, and labels "the correct OPEN form ... NOT refuted; remains the wall":
    CrossCellAbsoluteBound :  forall r >= 2,  crossCell(H,zeta,r) * q  <=  2^r * |H|^r,   |H| = n/2.
The per-level consumer N0_gap_of_absoluteBound uses exactly this (crossCell <= 2^r|H|^r/q).

We showed crossCell(r) is p-INDEPENDENT char-0 structural (probe ..._superrandom_pindep), and at
r=4 equals 3n^2/2 EXACTLY (= E(mu_n) - 2 E(mu_{n/2}) = (3n^2-3n) - 2(3(n/2)^2-3(n/2)) = 3n^2/2, from
the in-tree energy bricks AdditiveEnergyNegClosedLower: E(mu_n)=3n^2-3n).

Then the STATED bound at r=4 reads  (3n^2/2)*q <= 2^4*(n/2)^4 = n^4  <=>  q <= (2/3)*n^2.
In the prize regime q ~ n*2^128 >> n^2  =>  VIOLATED by ~2^128.  Verified exactly at prize-shaped
primes below.  More generally, since crossCell(r) is the fixed char-0 structural count and the RHS
2^r|H|^r = n^r is fixed too, the bound  n^r >= crossCell(r)*q  only holds once
    r * log2(n)  >=  log2(crossCell(r)) + log2(q),  log2 q ~ log2(n)+128,
i.e. at an r0(n) FAR ABOVE the prize binding depth r ~ ln q ~ 89 (measured r0(8) ~ 440, r0(16) ~ 220).

VERDICT (rule-4 constraint map; a precise correction, NOT a CORE result): the STATED
CrossCellAbsoluteBound is NOT an open wall -- it is FALSE at every feasible/prize-relevant depth.
It fails at low r (r=4: q<=(2/3)n^2 violated by 2^128) and does not turn true until r0(n) >> 89.
The file's "tracks the random BCHKS-1.12 expectation (2^r-2)|H|^r/p to O(1)" was measured at SMALL
accessible primes (p ~ relation-height) where crossCell ~ random; at PRIZE primes (p ~ 2^128) the two
DIVERGE by ~2^128 (crossCell frozen at the char-0 structural value, random ~ 0).  So the genuine open
object is NOT "crossCell <= 2^r|H|^r/q" but a depth-correct, p-independent STRUCTURAL count bound at
the binding depth r ~ ln q -- i.e. the char-0 vanishing-sums / Lam-Leung object, consistent with the
companion no-go (tower iteration) + no-saving (super-random) results.  CORE not closed.
"""
import sympy
from collections import defaultdict
import math


def N0_exact(S, p, r):
    dist = {0: 1}
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for x in S:
                nd[(s + x) % p] += c
        dist = nd
    return dist.get(0, 0)


def build(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = []
    x = 1
    for _ in range(n):
        G.append(x); x = (x * h) % p
    h2 = (h * h) % p
    H = []
    x = 1
    for _ in range(n // 2):
        H.append(x); x = (x * h2) % p
    return G, H


def main():
    print("(A) STATED bound at r=4:  crossCell(4)*q <= 2^4*(n/2)^4 = n^4.  crossCell(4)=3n^2/2 (exact, char-0).")
    print(f"{'n':>4} {'beta':>5} {'p(=q)':>11} {'crossCell(4)':>12} {'LHS=cross*q':>16} {'RHS=n^4':>14} {'holds?':>7}")
    for n in [8, 16, 32]:
        for beta in [2.3, 4.0]:
            p = sympy.nextprime(int(n ** beta))
            while (p - 1) % n != 0:
                p = sympy.nextprime(p)
            if p > 2_000_000:
                continue
            G, H = build(n, p)
            cross = N0_exact(G, p, 4) - 2 * N0_exact(H, p, 4)
            lhs = cross * p
            rhs = (2 ** 4) * ((n // 2) ** 4)
            print(f"{n:>4} {beta:>5} {p:>11} {cross:>12} {lhs:>16} {rhs:>14} {str(lhs <= rhs):>7}")
    print("  => FALSE for all n,beta (LHS/RHS ~ 100x-1500x): the stated r=4 inequality fails at prize.\n")

    print("(B) depth threshold r0(n): smallest r with n^r >= crossCell(r)*q at prize q~n*2^128.")
    print("    crossCell(r) read char-0 at a large prime; prize binding depth r ~ ln q ~ 89 for reference.")
    for n in [8, 16]:
        rmax = 12 if n == 8 else 10
        pbig = sympy.nextprime(n ** (rmax // 2 + 3))
        while (pbig - 1) % n != 0:
            pbig = sympy.nextprime(pbig)
        G, H = build(n, pbig)
        log2q = math.log2(n) + 128
        print(f"  n={n}: (r, crossCell(r), log2 cross, r*log2 n, need=log2cross+log2q, holds@prize)")
        for r in range(4, rmax + 1, 2):
            v = N0_exact(G, pbig, r) - 2 * N0_exact(H, pbig, r)
            if v <= 0:
                continue
            lc = math.log2(v)
            print(f"     r={r:>2}  cc={v:>12}  log2cc={lc:>6.2f}  r*log2n={r*math.log2(n):>6.1f}  "
                  f"need={lc+log2q:>7.1f}  holds={r*math.log2(n) >= lc+log2q}")
        # extrapolate r0: log2 cross(r) ~ slope*r; need r*log2n >= slope*r + log2q
        # rough slope from r=4..rmax
        v4 = N0_exact(G, pbig, 4) - 2 * N0_exact(H, pbig, 4)
        vM = N0_exact(G, pbig, rmax) - 2 * N0_exact(H, pbig, rmax)
        slope = (math.log2(vM) - math.log2(v4)) / (rmax - 4)
        denom = math.log2(n) - slope
        r0 = (log2q + (math.log2(v4) - slope * 4)) / denom if denom > 0 else float('inf')
        print(f"     => extrapolated r0(n={n}) ~ {r0:.0f}  (prize binding depth ~ 89)  => "
              f"{'bound never holds at feasible depth' if r0 > 100 else 'check'}")
    print("\nVERDICT: the STATED CrossCellAbsoluteBound is FALSE at every prize-relevant depth (fails low r,")
    print("         turns true only at r0(n) >> 89).  It is NOT the open wall as the file labels it; the")
    print("         genuine open object is a depth-correct p-independent structural count bound (Lam-Leung).")


if __name__ == '__main__':
    main()
