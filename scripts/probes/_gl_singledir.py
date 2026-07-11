#!/usr/bin/env python3
"""
SINGLE-DIRECTION exact D via NECKLACE (orbit-representative) enumeration. True n x speedup:
we enumerate subsets up to the cyclic shift by fixing index 0 in the subset and taking a canonical
rotation, then weight each orbit by its true size.  Restricted to ONE direction (a,b) (default the
binding low pair b=k, a sweeps) so we can push n far while staying EXACT.
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
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): S.append(x); x = x*h % p
        if len(set(S)) == n: return S, h
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

def gamma_for_R(R, p, k, prec_a, prec_b, Vrows):
    s = len(R)
    V = [Vrows[i] for i in R]
    P = left_null(V, p)
    if not P: return ('none', None)
    pa = [sum(P[t][ii] * prec_a[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    pb = [sum(P[t][ii] * prec_b[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    if not any(pb):
        if not any(pa): return ('heavy', None)
        return ('none', None)
    i = next(j for j in range(len(pb)) if pb[j])
    g = (-pa[i] * pow(pb[i], p - 2, p)) % p
    if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
        return ('one', g)
    return ('none', None)

def D_dir(S, h, p, k, a, b, s):
    """exact distinct-gamma for ONE direction via necklace enumeration (canonical rep min-tuple)."""
    n = len(S)
    prec_a = [pow(x, a, p) for x in S]; prec_b = [pow(x, b, p) for x in S]
    Vrows = {i: [pow(S[i], j, p) for j in range(k)] for i in range(n)}
    fac = pow(h, (b - a) % n, p)
    gammas = set(); heavy = False
    seen = set()
    # necklace: iterate subsets containing 0 as their canonical min-rotation
    for rest in itertools.combinations(range(1, n), s-1):
        R = (0,) + rest
        # canonical check: is R the lexicographically-smallest rotation?
        canon = min(tuple(sorted((i-c) % n for i in R)) for c in R)  # rotate so each elt ->0
        if canon != tuple(sorted(R)):
            continue
        if tuple(sorted(R)) in seen: continue
        seen.add(tuple(sorted(R)))
        kind, g = gamma_for_R(R, p, k, prec_a, prec_b, Vrows)
        if kind == 'heavy': heavy = True; continue
        if kind == 'one':
            x = g
            for _ in range(n):
                gammas.add(x); x = (x*fac) % p
    if heavy: return p
    return len(gammas)

def run(n, k, s_lo, s_hi, b, p=None):
    p = p or fp(n, 200003)
    S, h = subgroup_ordered(p, n)
    print(f"[n={n} k={k} b={b} p={p}] single-dir D (max over offset a):", flush=True)
    res={}
    for s in range(s_lo, s_hi+1):
        best=(-1,None)
        for a in range(n):
            if a==b: continue
            D = D_dir(S, h, p, k, a, b, s)
            if D>best[0]: best=(D,a)
        res[s]=best
        print(f"  s={s} r={n-s} m={s-k}: D={best[0]} (a={best[1]}) {'GOOD' if best[0]<=n else 'bad'}", flush=True)
    return res

if __name__ == '__main__':
    n=int(sys.argv[1]); k=int(sys.argv[2]); s_lo=int(sys.argv[3]); s_hi=int(sys.argv[4])
    b=int(sys.argv[5]) if len(sys.argv)>5 else k
    run(n,k,s_lo,s_hi,b)
