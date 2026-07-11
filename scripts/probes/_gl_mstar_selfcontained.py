#!/usr/bin/env python3
"""
Self-contained m*(n) growth-law probe (no numpy / no prize_workspace import).
D(s) = max over FAR monomial directions of DISTINCT-gamma far-line incidence count,
where s = agreement-set size. D(s) is DECREASING in s.
s* = min{s : D(s) <= budget n} (smallest good agreement size = largest good radius r=n-s).
m* = s* - k.   delta* = (n-s*)/n = (1-rho) - m*/n.
GPU target: m*=3,3,5 at n=8,16,32  (=> s*=5,7,13, delta*=3/8,9/16,19/32).
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
    assert (p-1) % n == 0
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x = x*h % p; S.add(x)
        if len(S) == n: return sorted(S)
    raise RuntimeError(f"no order-{n} subgroup in F_{p}")

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

def incidence_s(Sint, p, k, a, b, s, pa_, pb_, Vrows):
    n = len(Sint); good = set()
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

def D_at_s(Sint, p, k, s, prec, Vrows):
    n = len(Sint); best = (-1, None)
    for b in range(k, s):
        pb_ = prec[b]
        for a in range(n):
            if a == b: continue
            c, sat = incidence_s(Sint, p, k, a, b, s, prec[a], pb_, Vrows)
            if sat: return (p, (a, b))
            if c > best[0]: best = (c, (a, b))
    return best

def run(n, k, p, budget, smax=None):
    Sint = [int(x) for x in subgroup(p, n)]
    prec = {e: [pow(x, e, p) for x in Sint] for e in range(n)}
    Vrows = {i: [pow(Sint[i], j, p) for j in range(k)] for i in range(n)}
    smax = smax or (n - k + 1)
    print(f"[n={n} k={k} rho={k}/{n} p={p} budget={budget}] sweep s upward:", flush=True)
    sstar = None
    for s in range(k + 1, smax + 1):
        D, binder = D_at_s(Sint, p, k, s, prec, Vrows)
        r = n - s; good = (D <= budget)
        print(f"  s={s} r={r} (m={s-k}): D={D} binder={binder} {'GOOD' if good else 'bad'}", flush=True)
        if good:
            sstar = s; break
    if sstar:
        mstar = sstar - k; ds = (n - sstar)/n
        print(f"  => s*={sstar}, m*={mstar}, delta*={ds} = (1-{k}/{n}) - {mstar}/{n}", flush=True)
        return sstar, mstar, ds
    print("  no good s found", flush=True)
    return None, None, None

if __name__ == '__main__':
    ns = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [8, 16]
    for n in ns:
        k = n // 4
        p = fp(n, 200003)
        run(n, k, p, n)
