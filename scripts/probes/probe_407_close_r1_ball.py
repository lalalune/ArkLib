#!/usr/bin/env python3
"""
probe_407_close_r1_ball.py  (#407 R1 — monomial extremality, precomputed deep-band ball)

Builds the deep-band syndrome ball  B = { [G_S * h]_{>=k} : |S|=a, h monic deg m=a*-a }
ONCE as a set in coeff-space V=F_q^{n-k}.  Then for ANY pencil (high-coeff vectors s0,s1):
   #bad = #{ gamma : s0 + gamma*s1 in B }      (line-ball incidence, O(p) lookups)
   far(U) <=> [U]_{>=k} NOT in B               (U itself not within radius -> far direction)

R1 (far-direction): among GENUINE FAR pencils of fixed leading degrees (a*,b*), the
monomial line (s0=e_{a*}, s1=e_{b*}) maximizes #bad.  Adversarial sweep; any far excess
REFUTES R1.  We also print the incidence as the line is perturbed off the monomial.
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
def poly_mul(A, B, p):
    C = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        if a:
            for j, b in enumerate(B):
                C[i + j] = (C[i + j] + a * b) % p
    return C
def Gs_coeffs(S, mu, p):
    poly = [1]
    for i in S:
        poly = poly_mul(poly, [(-mu[i]) % p, 1], p)
    return poly
def high(coeffs, k, n):
    return tuple((coeffs[d] if d < len(coeffs) else 0) for d in range(k, n))

def build_ball(mu, k, p, a, m):
    """B = { [G_S h]_{>=k} : |S|=a, h monic deg m }.  Returns a set of tuples (len n-k)."""
    n = len(mu); B = set()
    hs = [[1]] if m == 0 else [list(c) + [1] for c in itertools.product(range(p), repeat=m)]
    for S in combinations(range(n), a):
        G = Gs_coeffs(S, mu, p)
        for h in hs:
            full = G if m == 0 else poly_mul(G, h, p)
            B.add(high(full, k, n))
    return B

def line_incidence(s0, s1, p, B):
    n_k = len(s0); cnt = 0
    for gamma in range(p):
        pt = tuple((s0[i] + gamma * s1[i]) % p for i in range(n_k))
        if pt in B: cnt += 1
    return cnt

def hv(coeffs_dict, k, n):
    return tuple(coeffs_dict.get(d, 0) for d in range(k, n))

def main():
    random.seed(5)
    n, k = 16, 4
    for p in [97, 193, 257, 337, 433]:
        if (p - 1) % n: continue
        mu = rou(p, n)
        print(f"\n=== p={p} RS[mu_{n},k={k}] ===", flush=True)
        for (astar, bstar) in [(9,5),(7,5),(11,9),(11,5),(13,9),(13,5),(15,11),(15,9),(15,5)]:
            for m in [1]:                    # deep band cofactor degree (m=1: fast, nonzero)
                a = astar - m
                if a <= k: continue
                B = build_ball(mu, k, p, a, m)
                def far(u): return hv(u, k, n) not in B
                if not (far({astar:1}) and far({bstar:1})):
                    continue
                s0m = hv({astar:1}, k, n); s1m = hv({bstar:1}, k, n)
                bc_mono = line_incidence(s0m, s1m, p, B)
                if bc_mono == 0: continue
                # adversarial candidates: keep leading degrees a*,b*; add lower high terms
                cand = []
                lowdegs0 = [d for d in range(k, astar)]
                lowdegs1 = [d for d in range(k, bstar)]
                for d in lowdegs0:
                    for c in random.sample(range(1,p), min(p-1, 40)):
                        cand.append(({astar:1, d:c}, {bstar:1}))
                for d in lowdegs1:
                    for c in random.sample(range(1,p), min(p-1, 40)):
                        cand.append(({astar:1}, {bstar:1, d:c}))
                for _ in range(300):
                    u0 = {astar:1}; u1 = {bstar:1}
                    for d in lowdegs0:
                        if random.random() < .35: u0[d] = random.randrange(1, p)
                    for d in lowdegs1:
                        if random.random() < .35: u1[d] = random.randrange(1, p)
                    cand.append((u0, u1))
                excess = []; ties = 0; far_n = 0; skip = 0; below = 0
                for (u0c, u1c) in cand:
                    if not (far(u0c) and far(u1c)): skip += 1; continue
                    far_n += 1
                    bc = line_incidence(hv(u0c, k, n), hv(u1c, k, n), p, B)
                    if bc > bc_mono: excess.append((bc, u0c, u1c))
                    elif bc == bc_mono: ties += 1
                    else: below += 1
                tag = "R1-OK" if not excess else "*** R1 REFUTED ***"
                print(f"  (a*,b*)=({astar},{bstar}) a={a} m={m}: mono={bc_mono} far={far_n} "
                      f"(skip {skip}) ties={ties} below={below} excess={len(excess)} {tag}", flush=True)
                for bc, u0c, u1c in sorted(excess, key=lambda t: -t[0])[:5]:
                    print(f"      EXCESS bc={bc}: U0={u0c} U1={u1c}", flush=True)

if __name__ == "__main__":
    main()
