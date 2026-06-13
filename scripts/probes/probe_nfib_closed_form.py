#!/usr/bin/env python3
"""Probe (#389 prize): closed form for N_fib(s,r) = max subset-sum fibre of r-subsets
of mu_s (2-power s), char 0, via the Lam-Leung antipodal-singleton structure.

THEORY (Mann/Lam-Leung, 2-power roots): two r-subsets T,T' of mu_s have sum T = sum T'
iff T \ T' and T' \ T are unions of antipodal pairs {x,-x}={zeta^a,zeta^{a+s/2}}.  Hence
sum T depends only on the SINGLETON part S(T) = {x in T : -x notin T} (paired elements
cancel).  So
    N_fib(s,r) = max_lambda  sum_{S antipodal-free, |S|=r(mod2), sum S=lambda}
                                C(s/2 - |S|, (r-|S|)/2).
Leading candidate: lambda=0 (r even) -> S=empty -> C(s/2, r/2)  (= unions of r/2 antipodal
pairs = squaring-fibre-unions).

THIS PROBE: compute N_fib(s,r) EXACTLY (char 0, exact zeta arithmetic via the
zeta^{s/2}=-1 reduction) for 2-power s, ALL r, and compare to:
  (A) C(s/2, r/2)              [the lambda=0 / all-paired count, r even]
  (B) the full singleton formula max.
Reports the true max, the arg-max lambda, and whether (A) or (B) is the closed form.
"""
import itertools, sys
from math import comb
from collections import Counter


def nfib_exact(s):
    """exact N_fib(s,r) for all r, via char-0 zeta arithmetic (zeta^{s/2} = -1)."""
    h = s // 2
    # sum of subset (as exponents) -> reduced integer vector in basis zeta^0..zeta^{h-1}
    def vec(T):
        v = [0] * h
        for a in T:
            sign = -1 if (a // h) % 2 == 1 else 1
            v[a % h] += sign
        return tuple(v)
    out = {}
    for r in range(1, s + 1):
        fib = Counter()
        for T in itertools.combinations(range(s), r):
            fib[vec(T)] += 1
        out[r] = max(fib.values())
    return out


def singleton_formula(s, r):
    """max_lambda sum_{S} C(s/2-|S|,(r-|S|)/2), the antipodal-singleton closed form.
    Computed by grouping antipodal-free S by sum (char-0 exact)."""
    h = s // 2
    # antipodal-free S: at most one of {a, a+h} per pair; encode by choosing a subset of
    # the h pairs and a sign (which representative). Group by exact sum.
    def vec_of(elems):
        v = [0] * h
        for a in elems:
            sign = -1 if (a // h) % 2 == 1 else 1
            v[a % h] += sign
        return tuple(v)
    best = 0
    # iterate over |S| = j with j ≡ r (mod 2), j from (0 or 1) up to min(r, h)
    contrib = Counter()  # lambda -> total count
    jmax = min(r, h)
    for j in range(r % 2, jmax + 1, 2):
        if (r - j) % 2 != 0:
            continue
        pairs_left = h - j
        if (r - j) // 2 > pairs_left:
            continue
        cbin = comb(pairs_left, (r - j) // 2)
        if cbin == 0:
            continue
        # antipodal-free S of size j: choose j pairs out of h, and a representative each
        for pairset in itertools.combinations(range(h), j):
            for signs in itertools.product([0, 1], repeat=j):
                elems = [pairset[t] + signs[t] * h for t in range(j)]
                contrib[vec_of(elems)] += cbin
    return max(contrib.values()) if contrib else 0


def main():
    print(f"{'s':>3} {'r':>3} | {'N_fib(exact)':>12} {'C(s/2,r/2)':>11} {'singleton-max':>13}  verdict")
    for s in (4, 8, 16, 32):
        exact = nfib_exact(s)
        for r in range(2, min(s, 13)):
            ex = exact[r]
            cA = comb(s // 2, r // 2) if r % 2 == 0 else None
            cB = singleton_formula(s, r)
            cAs = str(cA) if cA is not None else "-"
            v = []
            if cA is not None and cA == ex:
                v.append("C(s/2,r/2)=N_fib")
            if cB == ex:
                v.append("singleton=N_fib")
            if cA is not None and cA != ex:
                v.append(f"C off by {ex-cA}")
            print(f"{s:>3} {r:>3} | {ex:>12} {cAs:>11} {cB:>13}  {'; '.join(v)}", flush=True)
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
