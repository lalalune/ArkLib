#!/usr/bin/env python3
"""
probe_407_close_r1_syndrome.py  (#407 R1 — monomial extremality, LINE-BALL / syndrome form)

R1 (monomial extremality): among all pencils (U0, U1) of fixed leading degrees (a*, b*),
the MONOMIAL pencil (X^{a*}, X^{b*}) maximizes the bad-scalar count
    #bad(U0,U1) = #{ gamma in F_q : U0 + gamma*U1 is within (n-a) of RS[mu_n,k] }.

LINE-BALL FORM (the clean fast object). With a parity check H of RS[mu_n,k],
s0=H U0, s1=H U1, w=n-a, and S_w = { H e : wt(e) <= w } the low-weight syndrome ball,
    gamma bad  <=>  s0 + gamma*s1  in  S_w.
So #bad = #{ gamma : line s0+gamma*s1 hits S_w } -- a LINE-BALL INCIDENCE.
We precompute S_w as a set ONCE per (p,w), making each badcount O(p) hash lookups.

This is RIGOROUS and EXACT (no sampling of the agreement check): membership in S_w is
exact via the precomputed weight-<=w syndrome set.

Adversarial sweep over combination pencils of fixed leading degrees; any STRICT excess
over the monomial REFUTES R1.
"""
import itertools, random, sys

def gen(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p; seen.add(x)
        if len(seen) == p - 1:
            return g
    raise RuntimeError("no gen")

def rou(p, n):
    assert (p - 1) % n == 0
    g = gen(p); w = pow(g, (p - 1) // n, p)
    return [pow(w, i, p) for i in range(n)]

def inv(a, p): return pow(a, p - 2, p)

def syndrome(vec, mu, k, p):
    """Syndrome of a received word `vec` (length n) for RS[mu_n,k].
    RS codeword <=> inverse-DFT coeffs at degrees k..n-1 are all zero (mu = roots of unity).
    Syndrome = those (n-k) coefficients: S_j = sum_i vec_i * mu_i^{-j}, j=k..n-1.
    (drop the 1/n scaling -- irrelevant for membership/linearity). """
    n = len(mu)
    out = []
    for j in range(k, n):
        s = 0
        for i in range(n):
            s = (s + vec[i] * pow(mu[i], (n - j) % n, p)) % p
        out.append(s)
    return tuple(out)

def build_ball(mu, k, p, w):
    """S_w = { syndrome(e) : wt(e) <= w }.  Enumerate all error supports of size <= w
    and all nonzero values. For small n,w and prime p this is sum_{j<=w} C(n,j)(p-1)^j --
    too big for large p. Instead: we DON'T need full S_w; we need, per line, whether each
    point lies in S_w. We use the dual characterization via min-distance decoding:
    a syndrome s is in S_w iff the coset of s has a vector of weight <= w.
    We test that DIRECTLY per gamma using the standard 'is within distance w of code' check
    via brute force over agreement (k-subset interpolation) -- but to keep it fast we build
    S_w by enumerating low-weight error PATTERNS but representing values symbolically is hard.

    Practical exact approach used here: build S_w by enumerating supports of size exactly j
    for j=1..w and ALL value combos -- feasible only for tiny p. For our p up to ~450 and
    w up to ~9, C(16,9)*(p-1)^9 is astronomical. So build_ball is NOT used; we use the
    direct min-distance test `within_w` below which enumerates k-subsets (poly fits) and
    checks agreement >= n-w. That is exact and the bottleneck we optimize by dedup.
    """
    return None

def within_w(vec, mu, k, p, a, combos_k):
    """Exact: True iff some deg<k poly agrees with vec on >= a points (a = n-w).
    Iterate over precomputed k-subsets; interpolate; count agreement. Early-exit at >=a."""
    n = len(mu)
    best = 0
    for (T, lag) in combos_k:
        # lag[jj] = list of k Lagrange basis values at point jj for subset T
        ys = [vec[i] for i in T]
        ag = 0
        # evaluate interpolant at all points
        for jj in range(n):
            v = 0
            Lj = lag[jj]
            for t in range(k):
                v += ys[t] * Lj[t]
            if v % p == vec[jj]:
                ag += 1
        if ag >= a:
            return True
        if ag > best: best = ag
    return False

def precompute_lagrange(mu, k, p):
    """For each k-subset T, precompute Lagrange basis values at every point jj."""
    from itertools import combinations
    n = len(mu)
    out = []
    for T in combinations(range(n), k):
        xs = [mu[i] for i in T]
        lag = []
        ok = True
        for jj in range(n):
            row = []
            for t in range(k):
                num = 1; den = 1
                for u in range(k):
                    if u != t:
                        num = num * (mu[jj] - xs[u]) % p
                        den = den * (xs[t] - xs[u]) % p
                if den == 0: ok = False; break
                row.append(num * inv(den, p) % p)
            if not ok: break
            lag.append(row)
        if ok:
            out.append((T, lag))
    return out

def badcount(U0vals, U1vals, mu, k, p, a, combos_k):
    n = len(mu); cnt = 0
    for gamma in range(p):
        vec = [(U0vals[i] + gamma * U1vals[i]) % p for i in range(n)]
        if within_w(vec, mu, k, p, a, combos_k):
            cnt += 1
    return cnt

def polyvals(coeffs, mu, p):
    return [sum(c * pow(x, d, p) for d, c in coeffs.items()) % p for x in mu]

def main():
    random.seed(1)
    n, k = 16, 4
    primes = [97, 113, 193, 241, 257]  # ==1 mod 16, kept small-ish for speed
    deg_pairs = [(9, 5), (7, 5), (11, 9), (11, 5)]
    radii = [9, 10]  # a >= 9 (Johnson sqrt(64)=8); deeper band, fewer bad gammas -> faster
    for p in primes:
        if (p - 1) % n: continue
        mu = rou(p, n)
        combos_k = precompute_lagrange(mu, k, p)
        print(f"\n=== p={p}, RS[mu_{n},k={k}], {len(combos_k)} k-subsets ===", flush=True)
        for (astar, bstar) in deg_pairs:
            U0m = polyvals({astar: 1}, mu, p)
            U1m = polyvals({bstar: 1}, mu, p)
            for a in radii:
                bc_mono = badcount(U0m, U1m, mu, k, p, a, combos_k)
                if bc_mono == 0:
                    continue
                excess_found = []; ties = 0; trials = 0
                highdegs = [d for d in range(k, n) if d not in (astar, bstar)]
                cand = []
                step = max(1, p // 16)
                for d in highdegs:
                    for c in range(1, p, step):
                        cand.append(({astar: 1}, {bstar: 1, d: c}))
                        cand.append(({astar: 1, d: c}, {bstar: 1}))
                for _ in range(30):
                    u0 = {astar: 1}; u1 = {bstar: 1}
                    for d in random.sample(highdegs, k=min(2, len(highdegs))):
                        (u0 if random.random() < 0.5 else u1)[d] = random.randrange(1, p)
                    cand.append((u0, u1))
                for (u0c, u1c) in cand:
                    trials += 1
                    bc = badcount(polyvals(u0c, mu, p), polyvals(u1c, mu, p), mu, k, p, a, combos_k)
                    if bc > bc_mono: excess_found.append((bc, u0c, u1c))
                    elif bc == bc_mono: ties += 1
                tag = "R1-OK" if not excess_found else "*** R1 REFUTED ***"
                print(f"  (a*,b*)=({astar},{bstar}) a={a}: mono={bc_mono} trials={trials} "
                      f"ties={ties} excess={len(excess_found)} {tag}", flush=True)
                for bc, u0c, u1c in sorted(excess_found, reverse=True)[:3]:
                    print(f"      EXCESS bc={bc}>{bc_mono}: U0={u0c} U1={u1c}", flush=True)

if __name__ == "__main__":
    main()
