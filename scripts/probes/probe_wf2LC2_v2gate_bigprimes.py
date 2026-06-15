#!/usr/bin/env python3
"""
LANE LC2 (#407) — v2-gating at LARGE primes (beta 4..5) on the FIXED binding direction.

From probe_wf2LC2_v2gate_fast.py the binding monomial argmax is direction (9,15) with I_max=89,
identical across v2 in {4,5,6,7} at beta 3..4. Here we extend to beta~5 and high v2 (8,9,10),
testing the FIXED worst direction (9,15) incidence (cheap — one direction) plus a SPOT
re-confirmation that no monomial beats it (sampled top candidates), to see whether v2 EVER shifts
the binding incidence at prize beta.
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
    while p < pmin + 60_000_000:
        if p > 1 and isprime(p) and (p-1) % n == 0 and v2(p-1) == want_v2:
            return p
        p += n
    return None

if __name__ == '__main__':
    n, k, r = 16, 4, 10
    combos = list(itertools.combinations(range(n), n-r))
    a_dir, b_dir = 9, 15   # the binding worst monomial direction found by the full sweep
    # candidate beaters to spot-check (neighbors of the argmax)
    cand_dirs = [(9,15),(15,9),(8,15),(9,14),(10,15),(7,15),(9,13),(11,15),(8,14),(10,14)]
    print(f"n={n} k={k} r={r}  binding dir=({a_dir},{b_dir})  budget B={n}")
    print("Testing v2-spread at beta~4-5 (prize-faithful). I(dir) p-indep by construction.\n")
    targets = [
        (4, 70000), (6, 70000), (7, 70000), (8, 70000), (9, 70000), (10, 70000),  # beta~4
        (4, 1_050_000), (5, 1_050_000), (8, 1_050_000), (10, 1_050_000),          # beta~5
    ]
    rows = []
    for wv2, pmin in targets:
        p = find_prime(n, wv2, pmin)
        if p is None:
            print(f"   v2={wv2} pmin={pmin}: none"); continue
        mu = setup(n, p)
        best = 0; barg = None
        for (a,b) in cand_dirs:
            u0 = [pow(x,a,p) for x in mu]; u1 = [pow(x,b,p) for x in mu]
            I = incidence(u0, u1, mu, k, p, combos)
            if I < p and I > best: best = I; barg = (a,b)
        beta = math.log(p)/math.log(n)
        rows.append((wv2, p, beta, best, barg))
        print(f"   v2(p-1)={wv2:2d}  p={p:10d}  beta={beta:5.2f}  best-of-cands={best:4d}  arg={barg}")
    print()
    allI = sorted(set(I for _,_,_,I,_ in rows))
    print(f"distinct binding incidence across v2 in {sorted(set(w for w,_,_,_,_ in rows))}, beta 4..5: {allI}")
    if len(allI) == 1:
        print("VERDICT: binding incidence v2-BLIND & beta-BLIND at prize scale => delta* NOT v2-gated.")
    else:
        print("VERDICT: VARIES — inspect against v2 vs beta.")
