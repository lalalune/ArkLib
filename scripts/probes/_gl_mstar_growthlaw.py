#!/usr/bin/env python3
"""
GROWTH LAW of m*(n) for the p-INDEPENDENT distinct-gamma far-line incidence D.

Setup recap (all p-independent, char-0 combinatorial):
  s = agreement-set size, r = n - s = radius.  k = rho*n.  m = s - k = "binding depth".
  D(s) = max over FAR monomial directions (a,b) of the distinct-gamma incidence count.
  s* = min{ s : D(s) <= budget n },  m* = s* - k,  delta* = (n - s*)/n = (1-rho) - m*/n.

This script computes D(s) DIRECTLY (exact, over a single p, since p-independent) but with
the dilation-orbit acceleration MADE RIGOROUS so we can push n up:

  For direction (a,b), let d = (a - b) mod n.  Dilating a witness subset R by the cyclic
  generator h of mu_n maps the unique solution gamma_R -> h^{ -(a-b) } gamma_R = (a fixed scalar)^{-1} gamma_R.
  Wait -- precisely: replacing R (index set) by R+1 (shift) and re-deriving gamma multiplies
  gamma_R by h^{b-a} = h^{-d}.  So the distinct-gamma SET is a union of orbits of the
  multiplicative group < h^{-d} > of size n / gcd(n,d).  Hence:
      D(a,b;s) = (n / gcd(n,d)) * (number of dilation-orbits of witness subsets R that have a
                  genuine single gamma, counted up to the +1 shift, with one representative each).
  We DON'T need this to count (we just enumerate subsets), but we use gcd(n,d) | D as a CHECK.

The cheap census route (no F_p linear algebra, pure cyclotomic):
  At the binding ADJACENT-PAIR direction (b = k, a = k+1 say, or the empirically-binding low pair),
  a witness subset corresponds to an EXPONENT subset T of Z/n of size w = s, and the
  "single genuine gamma" survives iff the deg-<k vanishing of (x^a + gamma x^b) on the size-s set
  is consistent, which translates to a fixed list of ELEMENTARY-SYMMETRIC vanishing constraints on
  zeta^T (depth-m = e_2 .. e_{m+1} on the relevant root config), p-independently.

Plan:
  (A) For small n (8,16) directly recompute D(s) by full far-direction sweep (single p) -> ground truth.
  (B) Extract the binding direction & express D(s*) and D(s*-1) as census counts; verify equality.
  (C) Push the census to n = 24,36,40,48,... to get the m*(n) growth law.
"""
import sys, math, itertools

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s=0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def fp(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and isprime(p): return p
        p += n

def subgroup_ordered(p, n):
    """Return S with S[i] = h^i (cyclic, dilation by h = index +1)."""
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): S.append(x); x = x*h % p
        if len(set(S)) == n: return S
    raise RuntimeError("no subgroup")

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence_dir(S, p, k, a, b, s, prec, Vrows):
    n = len(S); good = set(); pa_ = prec[a]; pb_ = prec[b]
    for R in itertools.combinations(range(n), s):
        V = [Vrows[i] for i in R]
        P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): return p, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return len(good), False

def D_at_s_full(S, p, k, s, prec, Vrows):
    """Full far-direction sweep; return (D, binder, per_dir dict)."""
    n = len(S); best = (-1, None); perdir = {}
    for b in range(k, s):
        for a in range(n):
            if a == b: continue
            c, sat = incidence_dir(S, p, k, a, b, s, prec, Vrows)
            if sat: return (p, (a, b), perdir)
            perdir[(a,b)] = c
            if c > best[0]: best = (c, (a, b))
    return best[0], best[1], perdir

def run_full(n, k, p, budget, s_range):
    S = subgroup_ordered(p, n)
    prec = {e: [pow(x, e, p) for x in S] for e in range(n)}
    Vrows = {i: [pow(S[i], j, p) for j in range(k)] for i in range(n)}
    out = {}
    for s in s_range:
        D, binder, perdir = D_at_s_full(S, p, k, s, prec, Vrows)
        out[s] = (D, binder, perdir)
        r = n - s
        # gcd check on binder
        a,b = binder
        d = (a-b) % n; g = math.gcd(n,d); orbit = n//g
        print(f"[n={n} k={k}] s={s} r={r} m={s-k}: D={D} binder={binder} d={d} gcd={g} orbit_size={orbit} "
              f"{'<=n GOOD' if D<=budget else '>n bad'}", flush=True)
    return out

if __name__ == '__main__':
    import json
    n = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv)>2 else n//4
    p = fp(n, 200003); budget = n
    # sweep s from k+1 up to where D drops below n, plus one extra
    s_range = range(k+1, n-k+2)
    if len(sys.argv) > 4:
        s_range = range(int(sys.argv[3]), int(sys.argv[4])+1)
    run_full(n, k, p, budget, s_range)
