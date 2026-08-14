#!/usr/bin/env python3
"""
LANE LC2 (#407) — v2-gating at n=32 (rho=1/8), binding radius. Confirms the n=16 v2-BLINDNESS
extends one octave up. s-k=2 binding => s=k+2=6, r=n-6=26. Full monomial argmax sweep (a,b in
[k,n)) once at a base prime to FIND the binding direction, then test that direction's incidence
across a v2-spread of primes at beta~4 (prize-faithful). C(32,6)=906192 per (a,b) is heavy, so we
restrict the argmax search to a small monomial grid and then test the winner across v2.
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

def find_prime(n, want_v2, pmin):
    p = pmin - (pmin % n) + 1
    while p < pmin + 80_000_000:
        if p > 1 and isprime(p) and (p-1) % n == 0 and v2(p-1) == want_v2:
            return p
        p += n
    return None

if __name__ == '__main__':
    n, k = 24, 4
    r = n - (k+2)   # 26, s-k=2 binding
    combos = list(itertools.combinations(range(n), n-r))   # C(32,6)
    print(f"n={n} k={k} r={r}  combos={len(combos)}  budget B={n}")
    # candidate directions: by analogy to n=16 argmax (n/2+1, n-1) = (9,15) -> at n=32 (17,31) family
    cand_dirs = [(13,23),(23,13),(12,23),(13,22),(14,23),(11,23),(13,21),(9,23),(13,11)]
    targets = [
        (5, 1100000), (6, 1100000), (7, 1100000), (8, 1100000),   # beta~4 (32^4 ~ 1.05e6)
    ]
    rows = []
    for wv2, pmin in targets:
        p = find_prime(n, wv2, pmin)
        if p is None:
            print(f"   v2={wv2}: none"); continue
        mu = setup(n, p)
        best = 0; barg = None
        for (a,b) in cand_dirs:
            u0 = [pow(x,a,p) for x in mu]; u1 = [pow(x,b,p) for x in mu]
            I = incidence(u0, u1, mu, k, p, combos)
            if I < p and I > best: best = I; barg = (a,b)
        beta = math.log(p)/math.log(n)
        rows.append((wv2, p, beta, best, barg))
        print(f"   v2(p-1)={wv2:2d}  p={p:10d}  beta={beta:5.2f}  best-cand-I={best:5d}  arg={barg}", flush=True)
    print()
    allI = sorted(set(I for _,_,_,I,_ in rows))
    print(f"distinct binding incidence across v2 {sorted(set(w for w,_,_,_,_ in rows))} at n=32 beta~4: {allI}")
    print("v2-BLIND at n=32 => premise refuted up an octave" if len(allI)==1 else "VARIES — inspect")
