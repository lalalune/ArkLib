#!/usr/bin/env python3
"""
door-(iv) Lane-1 — NON-NEGATION-STABLE decomposition coherence.

CONTEXT (the surviving direction the campaign NAMED, never probed):
  The raw index-2 coset-half split of mu_n (n=2^a) is DEGENERATE: every nontrivial
  subgroup of the cyclic 2-group mu_n CONTAINS the unique order-2 element -1 = g^{n/2},
  so both half-period sums are REAL, and whenever they share a sign rho(b)=1 exactly
  (DISPROOF_LOG [door-iv-coset-half-degeneracy], kernel DoorIVCosetHalfCoherence).
  The VERDICT there: "Any surviving door-(iv) theorem must use a finer/NON-negation-
  stable decomposition or a different arithmetic statistic of {b*x^m}; the two-half
  coherence by itself cannot be bounded below 1."

  This probe tests EXACTLY that named-but-unprobed surviving lever: split mu_n into
  pieces that are NOT closed under x -> -x, so the piece-sums are GENUINELY COMPLEX,
  and ask whether the worst-b coherence rho(b) = |sum pieces| / sum|pieces| has any
  USABLE SLACK (rho bounded below 1 uniformly), which a moment-free / completion-free
  anti-concentration could grip — OR whether it ALSO saturates to 1 (closing the lever).

NON-NEGATION-STABLE splits tested (none is a subgroup-coset, all break x->-x symmetry):
  S_HALF : exponent high-bit  P0={g^j: 0<=j<n/2}, P1={g^j: n/2<=j<n}  (an ARC, not a coset;
           note -g^j = g^{j+n/2} maps P0<->P1, so each piece is NOT negation-closed)
  S_QTR  : 4 arcs g^j by floor(4j/n)  (negation pairs P0<->P2, P1<->P3)
  K-piece arcs for K in {2,4,8} generalizing the above.

We measure, over ALL (p-1)/n multiplicative coset reps b (or a large sample), the WORST
(max) coherence rho_S(b) for each split S, in the PRIZE REGIME: PROPER thin mu_n (n=2^a),
p = 1 mod n, p >> n^3, m=(p-1)/n, NEVER n=q-1. Exact complex arithmetic via integer
residues b*x mod p and an exact e_p table.

HONESTY: probe-first, no formalization of any conjecture not observed. If rho saturates
to 1 the lever is dead (constraint lemma); if it has robust slack we report it WITHOUT
overclaiming a CORE bound.
"""
import cmath, math, sys

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    import random
    for _ in range(24):
        a = random.randrange(2, n-1)
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def find_prime(n, beta, tries=200000):
    # smallest p = 1 mod n with p ~ n^beta, p >> n^3
    target = int(n**beta)
    base = (target // n) * n + 1
    for k in range(tries):
        p = base + k*n
        if p > n**3 and p % n == 1 and is_prime(p):
            return p
    return None

def subgroup_mu_n(g, p, n):
    # mu_n = <g0> where g0 = primitive root ^((p-1)/n); return exponent-ordered list g0^j
    pr = primitive_root(p)
    g0 = pow(pr, (p-1)//n, p)
    return [pow(g0, j, p) for j in range(n)], g0

def primitive_root(p):
    # find a generator of F_p^*
    fac = factorize(p-1)
    for a in range(2, p):
        if all(pow(a, (p-1)//q, p) != 1 for q in fac):
            return a
    raise RuntimeError("no primitive root")

def factorize(m):
    fac = set(); d = 2
    while d*d <= m:
        while m % d == 0: fac.add(d); m//=d
        d += 1
    if m > 1: fac.add(m)
    return fac

def coherence_for_split(bvals_xlist, ep, pieces_idx):
    """given list of (b*x mod p) implicit via xlist and b, compute piece sums; here we
    pass precomputed e_p(b*x) per x. pieces_idx: list of index-lists into xlist."""
    pass

def run(n, beta, max_cosets=20000):
    p = find_prime(n, beta)
    if p is None:
        print(f"  n={n} beta={beta}: no prime found"); return
    m = (p-1)//n
    assert p % n == 1 and p > n**3 and n != p-1
    mu, g0 = subgroup_mu_n(None, p, n)   # exponent-ordered: mu[j] = g0^j
    # e_p table
    w = [cmath.exp(2j*math.pi*t/p) for t in range(p)]
    # multiplicative coset reps of F_p^*/mu_n: use g^c for c in 0..m-1 where g primitive root
    pr = primitive_root(p)
    # coset rep r_c = pr^c ; then b ranges over reps. |eta_b| invariant on mu_n-coset.
    # sample cosets if m too large
    import random
    creps = list(range(m))
    if m > max_cosets:
        creps = random.sample(creps, max_cosets)
    # split index sets on the EXPONENT j of mu (mu[j]=g0^j), arcs:
    def arc_pieces(K):
        P = [[] for _ in range(K)]
        for j in range(n):
            P[(K*j)//n].append(j)
        return P
    splits = {
        "ARC2": arc_pieces(2),
        "ARC4": arc_pieces(4),
        "ARC8": arc_pieces(8),
    }
    # also a negation-STABLE reference: subgroup index-2 coset (even/odd exponent) -> should give rho->1
    sub2 = [[j for j in range(n) if j%2==0],[j for j in range(n) if j%2==1]]
    splits["SUBGRP2(ref)"] = sub2
    worst = {k: (0.0, None) for k in splits}
    for c in creps:
        b = pow(pr, c, p)
        # eta pieces: for each x=mu[j], term = w[(b*mu[j])%p]
        terms = [w[(b*mu[j]) % p] for j in range(n)]
        for name, P in splits.items():
            psum = [sum(terms[j] for j in idx) for idx in P]
            num = abs(sum(psum))
            den = sum(abs(s) for s in psum)
            if den > 1e-12:
                rho = num/den
                if rho > worst[name][0]:
                    worst[name] = (rho, c)
    Msup = max(abs(sum(w[(pow(pr,c,p)*mu[j])%p] for j in range(n))) for c in creps)
    print(f"  n={n:3d} p={p:>12d} m={m:>10d} beta={math.log(p)/math.log(n):.3f} "
          f"M/sqrt(n)={Msup/math.sqrt(n):.2f} cosets_scanned={len(creps)}")
    for name in ["ARC2","ARC4","ARC8","SUBGRP2(ref)"]:
        r,c = worst[name]
        print(f"      worst rho [{name:13s}] = {r:.6f}   (1-rho = {1-r:.2e})")

if __name__ == "__main__":
    print("=== door-(iv) NON-negation-stable split coherence (worst-b rho) ===")
    print("ARC* = exponent-arc splits of mu_n (NOT subgroups, NOT negation-closed pieces)")
    print("SUBGRP2(ref) = even/odd exponent = the proven-degenerate negation-stable index-2 split\n")
    for (n,beta) in [(16,3.8),(16,4.3),(32,3.8),(32,4.2),(64,3.7),(64,4.0)]:
        run(n,beta)
