#!/usr/bin/env python3
"""
probe_407_close_r1_fardir.py  (#407 R1 — monomial extremality, FAR-DIRECTION constrained)

R1 must be stated for GENUINE FAR pencils.  The pencil { U0 + gamma*U1 } is a far coset
iff U1 itself is far (maxagree(U1) < a): otherwise U1 ~ near-codeword and almost every
gamma is bad (degenerate).  The naive sweep "refutes" R1 only via such degenerate U1
(e.g. X^5+X^13 = X^5(1+X^8) vanishes on half of mu_16) -- NOT a legitimate competitor.

CORRECT R1: among GENUINE FAR pencils (U0,U1) with maxagree(U0)<a, maxagree(U1)<a, of
the SAME leading degrees (deg U0=a*, deg U1=b*), the MONOMIAL pencil (X^{a*},X^{b*})
maximizes  #bad = #{ gamma : maxagree(U0+gamma U1) >= a }.

We test k=4 (genuine Kambire regime) at beyond-Johnson radii, with the far-direction
filter ENFORCED on every candidate.  Any genuine-far excess REFUTES R1.
"""
import itertools, random
from itertools import combinations

def gen(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p; seen.add(x)
        if len(seen) == p - 1: return g
    raise RuntimeError
def rou(p, n):
    g = gen(p); w = pow(g, (p - 1) // n, p); return [pow(w, i, p) for i in range(n)]
def inv(a, p): return pow(a, p - 2, p)

def precompute_lagrange(mu, k, p):
    n = len(mu); out = []
    for T in combinations(range(n), k):
        xs = [mu[i] for i in T]; lag = []; ok = True
        for jj in range(n):
            row = []
            for t in range(k):
                num = den = 1
                for u in range(k):
                    if u != t:
                        num = num * (mu[jj] - xs[u]) % p
                        den = den * (xs[t] - xs[u]) % p
                if den == 0: ok = False; break
                row.append(num * inv(den, p) % p)
            if not ok: break
            lag.append(row)
        if ok: out.append((T, lag))
    return out

def maxagree(vec, mu, k, p, combos_k, cap=None):
    n = len(mu); best = 0
    for (T, lag) in combos_k:
        ys = [vec[i] for i in T]
        ag = sum(1 for jj in range(n) if sum(ys[t] * lag[jj][t] for t in range(k)) % p == vec[jj])
        if ag > best:
            best = ag
            if cap is not None and best >= cap: return best
    return best

def evalvec(coeffs, mu, p):
    return [sum(c * pow(mu[i], d, p) for d, c in coeffs.items()) % p for i in range(len(mu))]

def badset(B0, B1, mu, k, p, a, combos_k):
    n = len(mu); bad = 0
    for gamma in range(p):
        vec = [(B0[i] + gamma * B1[i]) % p for i in range(n)]
        if maxagree(vec, mu, k, p, combos_k, cap=a) >= a:
            bad += 1
    return bad

def main():
    random.seed(11)
    n, k = 16, 4
    primes = [97, 193, 257]
    deg_pairs = [(9, 5), (7, 5), (11, 9), (11, 5), (13, 9)]
    radii = [9, 10, 11]   # deep band, beyond Johnson (sqrt(64)=8)
    for p in primes:
        if (p - 1) % n: continue
        mu = rou(p, n); combos = precompute_lagrange(mu, k, p)
        print(f"\n=== p={p} RS[mu_{n},k={k}] Johnson~8 ({len(combos)} subsets) ===", flush=True)
        for (astar, bstar) in deg_pairs:
            for a in radii:
                B0m = evalvec({astar: 1}, mu, p); B1m = evalvec({bstar: 1}, mu, p)
                # far-direction sanity for the monomial baseline
                ma0 = maxagree(B0m, mu, k, p, combos); ma1 = maxagree(B1m, mu, k, p, combos)
                if ma0 >= a or ma1 >= a:
                    print(f"  (a*,b*)=({astar},{bstar}) a={a}: monomial NOT far "
                          f"(ma0={ma0},ma1={ma1}) -- skip", flush=True)
                    continue
                bc_mono = badset(B0m, B1m, mu, k, p, a, combos)
                if bc_mono == 0: continue
                highdegs = [d for d in range(k, n) if d not in (astar, bstar)]
                cand = []
                # one extra high term on each side (sweep coeff), keep leading degree fixed
                step = max(1, p // 20)
                for d in highdegs:
                    if d < astar:  # adding a term below the leading degree keeps deg U0=a*
                        for c in range(1, p, step): cand.append(({astar: 1, d: c}, {bstar: 1}))
                    if d < bstar:
                        for c in range(1, p, step): cand.append(({astar: 1}, {bstar: 1, d: c}))
                # random multi-term perturbations (keep leading degrees)
                for _ in range(120):
                    u0 = {astar: 1}; u1 = {bstar: 1}
                    for d in highdegs:
                        if d < astar and random.random() < .3: u0[d] = random.randrange(1, p)
                        if d < bstar and random.random() < .3: u1[d] = random.randrange(1, p)
                    cand.append((u0, u1))
                excess = []; ties = 0; far = 0; nonfar = 0
                for (u0c, u1c) in cand:
                    B0 = evalvec(u0c, mu, p); B1 = evalvec(u1c, mu, p)
                    # ENFORCE far direction
                    if maxagree(B1, mu, k, p, combos, cap=a) >= a or \
                       maxagree(B0, mu, k, p, combos, cap=a) >= a:
                        nonfar += 1; continue
                    far += 1
                    bc = badset(B0, B1, mu, k, p, a, combos)
                    if bc > bc_mono: excess.append((bc, u0c, u1c))
                    elif bc == bc_mono: ties += 1
                tag = "R1-OK" if not excess else "*** R1 REFUTED (far-dir) ***"
                print(f"  (a*,b*)=({astar},{bstar}) a={a}: mono={bc_mono} far-cands={far} "
                      f"(nonfar-skip={nonfar}) ties={ties} excess={len(excess)} {tag}", flush=True)
                for bc, u0c, u1c in sorted(excess, key=lambda t: -t[0])[:5]:
                    print(f"      EXCESS bc={bc}: U0={u0c} U1={u1c}", flush=True)

if __name__ == "__main__":
    main()
