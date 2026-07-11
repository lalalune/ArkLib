#!/usr/bin/env python3
"""
probe_qline_census.py — EXACT census of the Theorem-Q deep-quotient line (R2 of the
second-moment front; companion to QuotientPerPrimeInstantiation.md / DISPROOF_LOG O44).

Question (decides which moment binds in the per-line three-moment chain): on the deep line
  u0(x) = x^{r m}/(x^m - w),   u1(x) = 1/(x^m - w),   w = z^m,  z^n != 1,
over the smooth domain H = mu_n (n = s*m, code dimension k = (r-1)m), do the
per-gamma lists stay tiny (singletons?), and is the UNION list over all gamma in F_p exactly
the structured family {q_S : S an r-subset of G} plus the known sub-witness marginal layer?

Method (exact, no sampling over gamma): a codeword c with agree(c, u0 + gamma*u1) >= a forces,
on every (k+1)-subset T' of its agreement set, the linear-in-gamma consistency condition
  sum_{x in T'} lam_x * (u0(x) + gamma*u1(x)) = 0,   lam_x = prod_{y in T', y != x} (x - y)^{-1}
(the finite-difference functional annihilating deg <= k-1 interpolation). Sweeping ALL
C(n, k+1) subsets T' therefore yields every gamma whose list is nonempty at radius
delta = 1 - a/n; per recovered gamma the exact list is computed by brute interpolation over
all k-subsets. This is exhaustive: every list element has >= a >= k+1 agreement points, so it
is seen by at least one T'.

Readouts at n = 16 (p = BabyBear, m = 2, s = 8, r = 5, k = 8, witness agreement a = rm = 10):
  - #distinct gamma with nonempty list at radius a, vs the constructed N0(8,5) = 40 bad scalars;
  - per-gamma list-size histogram at a (singletons certify 2nd moment = 1st moment at the floor);
  - union-list size + decomposition into {q_S} (computed from the construction) vs other;
  - the same at the sub-witness radius a - 1 (the marginal/C19-analogue layer).
Deterministic. Exit 0 = ran to completion (bookkeeping checks only; this MEASURES).
"""
import itertools
import math
import sys
from collections import Counter

P = 15 * (1 << 27) + 1  # BabyBear
N, M, R = 16, 2, 5
S_SUB = N // M          # |G| = 8
K = (R - 1) * M         # 8 (code degree bound: deg < K... here deg <= K-1; dim K)
A_WIT = R * M           # 10

FAIL = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


def inv(a):
    return pow(a, P - 2, P)


def order_gen(m):
    x = 3
    while True:
        g = pow(x, (P - 1) // m, P)
        if g != 1 and pow(g, m // 2, P) != 1:
            return g
        x += 1


def interp_eval(pts, vals, xs):
    """Lagrange-interpolate (pts, vals) (len = K) and evaluate at all xs. Exact mod P."""
    out = []
    for x in xs:
        tot = 0
        for i, (xi, yi) in enumerate(zip(pts, vals)):
            num, den = 1, 1
            for j, xj in enumerate(pts):
                if j == i:
                    continue
                num = num * ((x - xj) % P) % P
                den = den * ((xi - xj) % P) % P
            tot = (tot + yi * num % P * inv(den)) % P
        out.append(tot)
    return out


def main():
    g = order_gen(N)
    H = [pow(g, i, P) for i in range(N)]
    gG = pow(g, M, P)
    G = [pow(gG, i, P) for i in range(S_SUB)]
    # pick z with z^N != 1: deterministic small search; prefer good spread later if needed
    z = 5
    while pow(z, N, P) == 1:
        z += 1
    w = pow(z, M, P)
    u0 = [pow(x, R * M, P) * inv((pow(x, M, P) - w) % P) % P for x in H]
    u1 = [inv((pow(x, M, P) - w) % P) for x in H]

    # the structured family: q_S for each r-subset S of G, and its bad scalar
    structured = {}
    for S in itertools.combinations(G, R):
        # p_S(Y) = Y^R - prod(Y - a); q_S(x) = (p_S(x^m) - p_S(w)) / (x^m - w)
        def pS(y):
            pr = 1
            for a in S:
                pr = pr * ((y - a) % P) % P
            return (pow(y, R, P) - pr) % P
        lam = (-pS(w)) % P
        qvals = tuple((pS(pow(x, M, P)) - pS(w)) % P * inv((pow(x, M, P) - w) % P) % P
                      for x in H)
        structured[lam] = structured.get(lam, set()) | {qvals}
    n0 = len(structured)
    n0_monomial = sum(math.comb(S_SUB // 2, s) * 2 ** s
                      for s in range(R % 2, min(R, S_SUB - R) + 1, 2))
    print(f"deep-line constructed bad scalars: {n0} (C({S_SUB},{R}) = {math.comb(S_SUB, R)}; "
          f"the MONOMIAL line's count at the same parameters is N0({S_SUB},{R}) = {n0_monomial})")
    check("deep line realizes the full C(s,r) scalar count (> monomial N0)",
          n0 == math.comb(S_SUB, R) and n0 > n0_monomial,
          f"{n0} vs N0 = {n0_monomial}  [measured at this z only — no genericity claim]")

    # ---- the census: every (k+1)-subset of an agreement set certifies (gamma, interpolant)
    # directly, so one pass over C(n, k+1) subsets is exhaustive and cheap.
    def census(a_thresh):
        idx = list(range(N))
        per_gamma = {}
        union = set()
        degenerate = []
        for T in itertools.combinations(idx, K + 1):
            lam = []
            for i in T:
                den = 1
                for j in T:
                    if j != i:
                        den = den * ((H[i] - H[j]) % P) % P
                lam.append(inv(den))
            SA = sum(l * u0[i] % P for l, i in zip(lam, T)) % P
            SB = sum(l * u1[i] % P for l, i in zip(lam, T)) % P
            if SB == 0:
                degenerate.append((T, SA))
                continue
            gam = (-SA) * inv(SB) % P
            y = [(u0[i] + gam * u1[i]) % P for i in range(N)]
            pts = [H[i] for i in T[:K]]
            vals = [y[i] for i in T[:K]]
            ev = tuple(interp_eval(pts, vals, H))
            agree = sum(1 for i in range(N) if ev[i] == y[i])
            if agree >= a_thresh:
                per_gamma.setdefault(gam, set()).add(ev)
                union.add(ev)
        check(f"no degenerate (SA=SB=0 or SB=0) consistency subsets at thresh {a_thresh}",
              not degenerate, f"count = {len(degenerate)} (a degenerate subset would mean an "
              f"every-gamma layer the census cannot see)")
        return per_gamma, union

    print(f"\n== census at witness radius a = {A_WIT} (delta = {1 - A_WIT / N}) ==")
    pg, un = census(A_WIT)
    sizes = Counter(len(v) for v in pg.values())
    print(f"   gammas with nonempty list: {len(pg)}; per-gamma list sizes: {dict(sizes)}")
    print(f"   union list size: {len(un)}")
    struct_words = set()
    for v in structured.values():
        struct_words |= v
    in_struct = sum(1 for c in un if c in struct_words)
    print(f"   union ∩ structured q_S family: {in_struct} / {len(un)}")
    check("all constructed bad scalars recovered", set(structured) <= set(pg),
          f"missing: {len(set(structured) - set(pg))}")
    check("per-gamma lists at witness radius are singletons",
          all(len(v) == 1 for v in pg.values()),
          f"max = {max((len(v) for v in pg.values()), default=0)}")
    check("union list at witness radius = structured family exactly",
          un == struct_words, f"extra = {len(un - struct_words)}, missing = {len(struct_words - un)}")

    print(f"\n== census at sub-witness radius a = {A_WIT - 1} (the marginal layer) ==")
    pg2, un2 = census(A_WIT - 1)
    sizes2 = Counter(len(v) for v in pg2.values())
    print(f"   gammas with nonempty list: {len(pg2)}; per-gamma list sizes: {dict(sizes2)}")
    print(f"   union list size: {len(un2)}; ∩ structured: "
          f"{sum(1 for c in un2 if c in struct_words)}")
    big = {g_: v for g_, v in pg2.items() if len(v) > 1}
    print(f"   gammas with list > 1: {len(big)}; sizes: {sorted(len(v) for v in big.values())[-8:]}")

    print(f"\nfailures: {FAIL or 'none'}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
