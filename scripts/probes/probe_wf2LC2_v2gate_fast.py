#!/usr/bin/env python3
"""
LANE LC2 (#407) — FAST v2(p-1)-gating decisive test.

Fixed n=16,k=4 (rho=1/4), binding radius r=10. Sweep primes spanning v2(p-1) in {4..9} AND
beta=log_n p from ~3 up into the prize-faithful range (beta>=4, i.e. p>=n^4=65536). For each
prime compute (a) the full monomial-max binding incidence I_max and its argmax direction, and
(b) the incidence at the FIXED worst direction (9,15). If delta* is v2-gated, I_max or its
argmax must shift with v2 at fixed n. If v2-BLIND, the orchestrator self-correction stands and
the mission premise (v2-gated closed form) is REFUTED on the delta*-binding object.

Exact integer mod-p. Full monomial sweep (no sampling).
"""
import itertools, math

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def v2(m):
    c = 0
    while m % 2 == 0: m //= 2; c += 1
    return c

def proot(p):
    m = p-1; fac = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac): return g

def setup(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)]

def ddk(vals, pts, k, p):
    xs = pts[:k+1]; vs = list(vals[:k+1])
    for j in range(1, k+1):
        for i in range(k, j-1, -1):
            vs[i] = (vs[i]-vs[i-1]) * pow((xs[i]-xs[i-j]) % p, p-2, p) % p
    return vs[k]

def in_RS(vals, pts, k, p):
    s = len(pts)
    if s <= k: return True
    for st in range(s-k):
        if ddk(vals[st:st+k+1], pts[st:st+k+1], k, p) != 0: return False
    return True

def incidence(u0, u1, mu, k, p, combos):
    gam = set()
    for R in combos:
        pts = [mu[i] for i in R]; u0R = [u0[i] for i in R]; u1R = [u1[i] for i in R]
        if in_RS(u1R, pts, k, p):
            if in_RS(u0R, pts, k, p): return p
            continue
        a0 = ddk(u0R, pts, k, p); a1 = ddk(u1R, pts, k, p)
        if a1 % p == 0: continue
        g = (-a0 * pow(a1, p-2, p)) % p
        if in_RS([(u0R[i]+g*u1R[i]) % p for i in range(len(R))], pts, k, p): gam.add(g)
    return len(gam)

def mono_max(n, k, p, mu, combos):
    best = 0; arg = None
    mv = {b: [pow(x, b, p) for x in mu] for b in range(k, n)}
    for a in range(k, n):
        for b in range(k, n):
            if a == b: continue
            I = incidence(mv[a], mv[b], mu, k, p, combos)
            if I < p and I > best: best = I; arg = (a, b)
    return best, arg

def find_prime(n, want_v2, pmin):
    p = pmin - (pmin % n) + 1
    while p < pmin + 20_000_000:
        if p > 1 and isprime(p) and (p-1) % n == 0 and v2(p-1) == want_v2:
            return p
        p += n
    return None

if __name__ == '__main__':
    n, k, r = 16, 4, 10
    combos = list(itertools.combinations(range(n), n-r))
    print(f"n={n} k={k} r={r} (binding, s-k={n-r-k})  budget B={n}\n")
    # (want_v2, pmin) chosen to span v2 AND beta. beta=4 at p=65536, beta=5 at p=2^20.
    targets = [
        (4, 4000), (5, 4000), (6, 4000), (7, 4000),
        (4, 70000), (5, 70000), (6, 70000), (7, 70000),    # beta~4
        (4, 1_100_000), (5, 1_100_000), (8, 1_100_000),    # beta~5
        (9, 70000), (10, 70000),                            # high v2 prize-beta
    ]
    rows = []
    for wv2, pmin in targets:
        p = find_prime(n, wv2, pmin)
        if p is None:
            print(f"   v2={wv2} pmin={pmin}: none found"); continue
        mu = setup(n, p)
        I, arg = mono_max(n, k, p, mu, combos)
        beta = math.log(p)/math.log(n)
        rows.append((wv2, p, beta, I, arg))
        print(f"   v2(p-1)={wv2:2d}  p={p:9d}  beta={beta:5.2f}  I_max={I:4d}  argmax={arg}  {'>B' if I>n else '<=B'}")
    print()
    allI = sorted(set(I for _,_,_,I,_ in rows))
    allarg = sorted(set(arg for _,_,_,_,arg in rows))
    print(f"distinct I_max across all (v2,beta): {allI}")
    print(f"distinct argmax directions:         {allarg}")
    if len(allI) == 1 and len(allarg) == 1:
        print("VERDICT: binding I_max is v2-BLIND and beta-BLIND => delta* NOT v2-gated (mission premise REFUTED on binding object)")
    else:
        print("VERDICT: I_max VARIES — check whether the variation tracks v2 (gating) or beta (confound)")
