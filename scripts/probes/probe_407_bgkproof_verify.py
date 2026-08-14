#!/usr/bin/env python3
"""
ADVERSARIAL re-derivation of the #407 dyadic-BGK skeleton, from scratch.

Targets to independently verify or break:
  (V1) Parseval:  coll_r(p) = (1/p) sum_b |eta_b|^{2r}, and A_r = coll_r - n^{2r}/p.
  (V2) Ring decomposition: coll_r >= R_r, Anom_r := coll_r - R_r >= 0.
  (V3) Char-0 Wick:  R_r <= (2r-1)!! n^r.
  (V4) THE CLAIM:  A_r <= Wick  <=>  Anom_r <= n^{2r}/p.  (algebra check)
  (V5) The optimization:  M^{2r} <= p*A_r  with A_r<=Wick gives M <= C*sqrt(n log p)?
       and CRITICALLY: does the DC subtraction actually matter, or does MomentMethodNoGo
       (p*E_r)^{1/2r} >= n kill it anyway?
  (V6) Empirical A_r/Wick <= 1 and decreasing -- across regimes incl. the prize-shaped p=n^beta.

All exact (integer arithmetic for energies via FFT/convolution over Z/p... but energies are
over Z (ring) and Z/p (field). We compute eta_b exactly via complex FFT-like sums for the
sup-norm, and the collision counts via exact integer convolution.
"""
import numpy as np
import itertools, math
from math import comb

def doublefact_odd(twoR_minus_1):
    # (2r-1)!! for argument = 2r-1
    k = twoR_minus_1
    r = 1
    while k > 0:
        r *= k
        k -= 2
    return r

def wick(n, r):
    return doublefact_odd(2*r-1) * n**r

def roots_of_unity_modp(n, p):
    """Return the n distinct n-th roots of unity in F_p, given p ≡ 1 mod n prime."""
    assert (p-1) % n == 0
    # find a generator-ish element of order n: take g^((p-1)/n) for a primitive root g
    # brute force a primitive root
    def is_primroot(g):
        # check order = p-1
        seen = set()
        x = 1
        for _ in range(p-1):
            x = (x*g) % p
        return pow(g, p-1, p) == 1 and all(pow(g,(p-1)//q,p)!=1 for q in prime_factors(p-1))
    def prime_factors(m):
        f=set(); d=2
        while d*d<=m:
            while m%d==0:
                f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    g=2
    while not is_primroot(g):
        g+=1
    w = pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def eta_b(b, mu, p):
    """eta_b = sum_{x in mu} e_p(b x) = sum_x exp(2pi i b x / p)."""
    s = 0j
    for x in mu:
        s += np.exp(2j*np.pi*(b*x % p)/p)
    return s

def coll_r_exact(mu, p, r):
    """coll_r = #{(x,y) in mu^{2r}: sum x ≡ sum y mod p}.
    = (1/p) sum_b |eta_b|^{2r}, integer. Compute via convolution of the r-fold sum distribution mod p."""
    n = len(mu)
    # distribution of sum of r elements (with repetition, ordered -> just track counts) mod p
    # base: count of single element residues
    base = np.zeros(p, dtype=np.int64)
    for x in mu:
        base[x % p] += 1
    # r-fold convolution mod p
    dist = base.copy()
    for _ in range(r-1):
        dist = np.fft.irfft(np.fft.rfft(dist)*np.fft.rfft(base), n=p)
        dist = np.rint(dist).astype(np.int64)
    # coll_r = sum_s dist[s]^2  (pairs (x,y) with same sum residue)
    return int(np.sum(dist.astype(object)**2))

def coll_r_via_eta(mu, p, r):
    tot = 0.0
    for b in range(p):
        tot += abs(eta_b(b, mu, p))**(2*r)
    return tot/p

def zero_sum_count_ring(n, twoR):
    """R-side: #{(a_1..a_{2r}) in (Z/n)^{2r}: sum of zeta^{a_i} = 0 in Z[zeta_n]},
    BUT skeleton's R_r is #{(x,y) in mu^{2r}: sum x = sum y in Z[zeta]}.
    Via (x,y)->(x,-y) and negation-closure of mu_n (n even), R_r = zeroSumCount(2r):
      #{(c_1..c_{2r}) in mu_n^{2r} : sum c_i = 0 in Z[zeta_n]}.
    Compute exactly using the integer basis {zeta^j : 0<=j<n/2}, zeta^{n/2} = -1.
    Represent each root zeta^a (0<=a<n) as a length-(n/2) integer vector.
    Then count tuples whose vector sum is the zero vector. Use generating-function / DP over Z^{n/2}.
    For small n,r do exact DP with dict of vector-sums.
    """
    h = n//2
    # vector for zeta^a in basis {1, zeta, ..., zeta^{h-1}}, with zeta^h = -1
    def vec(a):
        a %= n
        v = [0]*h
        if a < h:
            v[a] = 1
        else:
            v[a-h] = -1
        return tuple(v)
    roots = [vec(a) for a in range(n)]
    # DP: dict mapping vector-sum -> count, over twoR steps
    from collections import defaultdict
    cur = {tuple([0]*h): 1}
    for _ in range(twoR):
        nxt = defaultdict(int)
        for s, cnt in cur.items():
            for rt in roots:
                ns = tuple(si+ri for si,ri in zip(s,rt))
                nxt[ns] += cnt
        cur = nxt
    return cur.get(tuple([0]*h), 0)

def A_r_exact(mu, p, r, n):
    coll = coll_r_exact(mu, p, r)
    return coll - (n**(2*r))/p, coll

print("="*78)
print("V1+V2+V3+V4: ring decomposition and the central algebraic reduction")
print("="*78)
cases = [(8,193),(8,257),(16,193),(16,257),(16,353)]
for n,p in cases:
    mu = roots_of_unity_modp(n,p)
    for r in range(1,5):
        coll = coll_r_exact(mu,p,r)
        Rr = zero_sum_count_ring(n, 2*r)  # over ring
        W = wick(n,r)
        Anom = coll - Rr
        Ar = coll - (n**(2*r))/p
        # V4 algebra: A_r <= Wick  <=>  Anom <= n^{2r}/p ?
        # A_r = R_r + Anom - n^{2r}/p. So A_r<=W  <=> R_r+Anom-n^{2r}/p <= W
        # The skeleton claims R_r<=W and then A_r<=W <== Anom<=n^{2r}/p.
        lhs_implies = (Anom <= (n**(2*r))/p)
        Ar_le_W = (Ar <= W + 1e-9)
        print(f"n={n} p={p} r={r}: coll={coll} R_r={Rr} Anom={Anom} Wick={W} "
              f"A_r={Ar:.3f}  R_r<=W:{Rr<=W}  Anom<=n^2r/p:{lhs_implies}  A_r<=W:{Ar_le_W}")
    print()
