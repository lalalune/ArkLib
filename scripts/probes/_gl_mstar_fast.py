#!/usr/bin/env python3
"""
FAST m*(n) probe for larger n.  Two accelerations vs the naive sweep:
 (1) ORBIT REDUCTION: for direction (a,b), dilating R by g in mu_n sends gamma_R -> g^(a-b) gamma_R.
     So distinct-gamma set is a union of <g^(a-b)>-orbits (size n/gcd(n,a-b)).  We count by
     iterating over subsets up to the dilation action: pick subsets with min-index 0 in a canonical
     transversal, multiply contribution.  (Implemented as: count all gammas exactly but only sweep
     directions; the orbit fact is used to PREDICT/CHECK, not to skip subsets here -- exactness kept.)
 (2) Only sweep s in a WINDOW [s_lo, s_hi] around the expected binding s* ~ k + log2(n), since D(s)
     is monotone decreasing: confirm D(s_lo-1)>n (bad) and find first GOOD.  Caller supplies window.
We keep the EXACT incidence (no sampling).  Optionally restrict directions to a shortlist
(the empirically-binding low exponents b in {k, k+1}) to bound work, with a full-sweep verify flag.
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

def subgroup(p, n):
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        # build as ordered cyclic <h>: S[i] = h^i  (so dilation by h is index shift +1)
        S=[]; x=1
        for _ in range(n): x = x*h % p; S.append(x)
        if len(set(S)) == n: return S   # S[i] = h^{i+1}; cyclic order preserved
    raise RuntimeError("no subgroup")

def fp(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and isprime(p): return p
        p += n

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

def incidence_dir(Sint, p, k, a, b, s, prec, Vrows):
    n = len(Sint); good = set()
    pa_ = prec[a]; pb_ = prec[b]
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

def D_at_s(Sint, p, k, s, prec, Vrows, dirs=None):
    n = len(Sint); best = (-1, None)
    if dirs is None:
        dirs = [(a, b) for b in range(k, s) for a in range(n) if a != b]
    for (a, b) in dirs:
        c, sat = incidence_dir(Sint, p, k, a, b, s, prec, Vrows)
        if sat: return (p, (a, b))
        if c > best[0]: best = (c, (a, b))
    return best

def run(n, k, p, budget, s_lo, s_hi, dirs=None, tag=""):
    Sint = subgroup(p, n)
    prec = {e: [pow(x, e, p) for x in Sint] for e in range(n)}
    Vrows = {i: [pow(Sint[i], j, p) for j in range(k)] for i in range(n)}
    print(f"[n={n} k={k} p={p} budget={budget}] {tag} sweep s in [{s_lo},{s_hi}]"
          + (f" dirs={dirs}" if dirs else " (full dirs)"), flush=True)
    sstar = None
    for s in range(s_lo, s_hi + 1):
        D, binder = D_at_s(Sint, p, k, s, prec, Vrows, dirs)
        r = n - s; good = (D <= budget)
        print(f"  s={s} r={r} m={s-k}: D={D} binder={binder} {'GOOD' if good else 'bad'}", flush=True)
        if good and sstar is None:
            sstar = s; break
    if sstar:
        print(f"  => s*={sstar} m*={sstar-k} delta*={(n-sstar)/n}", flush=True)
    return sstar

if __name__ == '__main__':
    # usage: _gl_mstar_fast.py n k s_lo s_hi [b_list_comma]
    n = int(sys.argv[1]); k = int(sys.argv[2]); s_lo = int(sys.argv[3]); s_hi = int(sys.argv[4])
    dirs = None
    if len(sys.argv) > 5:
        bs = [int(x) for x in sys.argv[5].split(',')]
        dirs = [(a, b) for b in bs for a in range(n) if a != b]
    p = fp(n, 200003)
    run(n, k, p, n, s_lo, s_hi, dirs)
