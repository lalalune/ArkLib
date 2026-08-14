#!/usr/bin/env python3
"""
probe_407_close_r1_enum.py  (#407 R1 — monomial extremality, FAST exact enumeration)

Exact bad-count via the polynomial-factorization view (NOT per-gamma agreement search):

  gamma bad for pencil (U0,U1) at agreement >= a  <=>  U0 + gamma*U1 - c = G_S * h
  for some a-subset S of mu_n (G_S = prod_{z in S}(X-z)), monic h of degree m=deg(U0)-a,
  and deg-<k c.  Comparing HIGH parts (deg >= k; low part absorbed by free c):
       s0 + gamma*s1 = [G_S * h]_{>=k}                                            (*)
  where s0=[U0]_{>=k}, s1=[U1]_{>=k} in coeff space.  For each (S,h) the RHS tau is a
  fixed vector; (*) has a solution gamma iff tau - s0 is parallel to s1, giving <=1 gamma
  (s1 != 0).  #bad = #distinct valid gamma over all (S,h).  EXACT and fast for small m.

We also verify against a direct per-gamma agreement count on a small case.

R1 (far-direction): among GENUINE FAR pencils of fixed leading degrees (a*,b*), the
monomial (X^{a*},X^{b*}) maximizes #bad.  Far = U0,U1 each far (own max-agreement < a).
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

def poly_mul(A, B, p):
    C = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        if a:
            for j, b in enumerate(B):
                C[i + j] = (C[i + j] + a * b) % p
    return C

def Gs_coeffs(S, mu, p):
    """coeffs (low->high) of prod_{i in S}(X - mu_i)."""
    poly = [1]
    for i in S:
        poly = poly_mul(poly, [(-mu[i]) % p, 1], p)
    return poly

def high_part(coeffs, k, n):
    """vector of coeffs at degrees k..n-1 (pad/truncate)."""
    return tuple((coeffs[d] if d < len(coeffs) else 0) for d in range(k, n))

def badset_enum(s0, s1, mu, k, p, a, astar, monic_hs, Gs_cache):
    """s0,s1: high-part vectors (tuples, indexed deg k..n-1). astar = deg U0 (=top of pencil).
    m = astar - a (cofactor degree). Returns set of bad gamma."""
    n = len(mu); m = astar - a
    # index of b* coordinate where s1 is nonzero: use the top nonzero coord of s1
    nz = [i for i in range(len(s1)) if s1[i] != 0]
    if not nz:
        return set()  # s1 high part zero -> not a far direction in this framing
    piv = nz[-1]; s1piv_inv = inv(s1[piv], p)
    bad = set()
    for S in combinations(range(n), a):
        G = Gs_cache[S]
        for h in monic_hs:
            full = poly_mul(G, h, p) if m > 0 else G
            tau = high_part(full, k, n)
            # require deg(full) == astar exactly (leading at astar), i.e. tau top coord matches
            if a + m != astar:  # safety
                continue
            # solve s0 + gamma s1 = tau  => gamma = (tau[piv]-s0[piv]) * s1piv_inv
            gamma = ((tau[piv] - s0[piv]) % p) * s1piv_inv % p
            ok = all((s0[i] + gamma * s1[i]) % p == tau[i] for i in range(len(s0)))
            if ok:
                bad.add(gamma)
    return bad

def monic_polys(m, p):
    """all monic polys of degree m (low->high), as coeff lists length m+1 with top=1."""
    if m == 0: return [[1]]
    out = []
    for coeffs in itertools.product(range(p), repeat=m):
        out.append(list(coeffs) + [1])
    return out

# --- verification against direct agreement count (small p) ---
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
                        num = num * (mu[jj] - xs[u]) % p; den = den * (xs[t] - xs[u]) % p
                if den == 0: ok = False; break
                row.append(num * inv(den, p) % p)
            if not ok: break
            lag.append(row)
        if ok: out.append((T, lag))
    return out
def maxagree(vec, mu, k, p, combos, cap=None):
    n = len(mu); best = 0
    for (T, lag) in combos:
        ys = [vec[i] for i in T]
        ag = sum(1 for jj in range(n) if sum(ys[t]*lag[jj][t] for t in range(k))%p==vec[jj])
        if ag > best:
            best = ag
            if cap and best >= cap: return best
    return best
def evalvec(coeffs, mu, p):
    return [sum(c*pow(mu[i],d,p) for d,c in coeffs.items())%p for i in range(len(mu))]
def badset_direct(u0, u1, mu, k, p, a, combos):
    B0 = evalvec(u0, mu, p); B1 = evalvec(u1, mu, p); bad = set()
    for g in range(p):
        vec = [(B0[i] + g*B1[i]) % p for i in range(len(mu))]
        if maxagree(vec, mu, k, p, combos, cap=a) >= a: bad.add(g)
    return bad

def coeffdict_to_high(u, k, n):
    return tuple(u.get(d, 0) for d in range(k, n))

def main():
    random.seed(3)
    n, k = 16, 4
    # --- VERIFY enum == direct on a tiny case (p=97, monomial (9,5), a=9) ---
    p = 97; mu = rou(p, n); combos = precompute_lagrange(mu, k, p)
    Gs_cache = {S: Gs_coeffs(S, mu, p) for S in combinations(range(n), 9)}
    s0 = coeffdict_to_high({9:1}, k, n); s1 = coeffdict_to_high({5:1}, k, n)
    be = badset_enum(s0, s1, mu, k, p, 9, 9, monic_polys(0, p), Gs_cache)
    bd = badset_direct({9:1}, {5:1}, mu, k, p, 9, combos)
    print(f"VERIFY a=9 monomial(9,5): enum={sorted(be)} direct={sorted(bd)} MATCH={be==bd}", flush=True)

    # --- R1 adversarial via FAST enum, far-direction enforced, several (a*,b*), deep a ---
    for p in [97, 193, 257, 337]:
        if (p-1) % n: continue
        mu = rou(p, n); combos = precompute_lagrange(mu, k, p)
        print(f"\n=== p={p} RS[mu_{n},k={k}] ===", flush=True)
        for (astar, bstar) in [(9,5),(7,5),(11,9),(11,5),(13,9),(13,5),(15,9)]:
            for a in [astar, astar-1]:   # m=0 and m=1 (deep band)
                if a <= k: continue
                Gs_cache = {S: Gs_coeffs(S, mu, p) for S in combinations(range(n), a)}
                hs = monic_polys(astar - a, p)
                def far(u):
                    return maxagree(evalvec(u, mu, p), mu, k, p, combos, cap=a) < a
                if not (far({astar:1}) and far({bstar:1})):
                    continue
                s0m = coeffdict_to_high({astar:1}, k, n); s1m = coeffdict_to_high({bstar:1}, k, n)
                bc_mono = len(badset_enum(s0m, s1m, mu, k, p, a, astar, hs, Gs_cache))
                if bc_mono == 0: continue
                highdegs = [d for d in range(k, n)]
                cand = []
                for d in highdegs:
                    if d < astar:
                        for c in random.sample(range(1,p), min(p-1, 30)):
                            cand.append(({astar:1, d:c}, {bstar:1}))
                    if d < bstar:
                        for c in random.sample(range(1,p), min(p-1, 30)):
                            cand.append(({astar:1}, {bstar:1, d:c}))
                for _ in range(150):
                    u0 = {astar:1}; u1 = {bstar:1}
                    for d in highdegs:
                        if d < astar and random.random()<.3: u0[d]=random.randrange(1,p)
                        if d < bstar and random.random()<.3: u1[d]=random.randrange(1,p)
                    cand.append((u0,u1))
                excess=[]; ties=0; far_n=0; skip=0
                for (u0c,u1c) in cand:
                    if not (far(u0c) and far(u1c)): skip+=1; continue
                    far_n+=1
                    s0=coeffdict_to_high(u0c,k,n); s1=coeffdict_to_high(u1c,k,n)
                    bc=len(badset_enum(s0,s1,mu,k,p,a,astar,hs,Gs_cache))
                    if bc>bc_mono: excess.append((bc,u0c,u1c))
                    elif bc==bc_mono: ties+=1
                tag = "R1-OK" if not excess else "*** R1 REFUTED ***"
                print(f"  (a*,b*)=({astar},{bstar}) a={a} (m={astar-a}): mono={bc_mono} "
                      f"far-cands={far_n} (skip {skip}) ties={ties} excess={len(excess)} {tag}", flush=True)
                for bc,u0c,u1c in sorted(excess,key=lambda t:-t[0])[:5]:
                    print(f"      EXCESS bc={bc}: U0={u0c} U1={u1c}", flush=True)

if __name__ == "__main__":
    main()
