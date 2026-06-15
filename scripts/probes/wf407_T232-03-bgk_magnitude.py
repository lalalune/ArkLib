#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : EXACT magnitude of the BGK kernel
    M(n, p) = | mu_n  cap  -(1 + mu_n) |
            = #{ u in mu_n : -(1+u) in mu_n }
            = #{ u in mu_n :  (1+u) in mu_n }   (since -1 in mu_n for even n)

In-tree (AdditiveEnergyKernel.lean): tripleZero(n) = #{(x,y,z) in mu_n^3 : x+y+z=0} = n * M(n,p).
Known structural facts (all proven in-tree):
  * M = 0 in char 0 (coprimality of X^n-1 and (X+1)^n-1).
  * M >= 1 (u=1 solution) iff char p | 2^n - 1  (Mersenne / Fermat-factor obstruction).
  * M even unless (2:F)^n = 1; 3|M when char != 3 and 3 (does not divide) n; hence 6|M generically.

GOAL: exact magnitude across primes for n=8,16,32,64.
  (1) distribution of M and its dependence on p,
  (2) connect to additive energy E_2 and the Fermat-curve count,
  (3) is M bounded non-trivially in the prize regime, or Mersenne/KSV wall?

We work in F_p (prime field). mu_n exists iff n | p-1. We enumerate ALL such primes up to a cap
(exact, not sampled), compute M exactly, and tabulate.
"""

import sys
from sympy import primerange, isprime, divisors

def mu_n(n, p):
    """The n-th roots of unity in F_p as a *set* of residues. Requires n | p-1.
       g a generator of F_p^*, then mu_n = { g^{(p-1)/n * j} : j } ."""
    # find a primitive root the cheap way (p small)
    # multiplicative group is cyclic of order p-1
    order = p - 1
    # factor order
    def is_primroot(g):
        # g is a primitive root iff for every prime q | order, g^{order/q} != 1
        seen = set()
        m = order
        qs = []
        d = 2
        mm = m
        while d*d <= mm:
            if mm % d == 0:
                qs.append(d)
                while mm % d == 0:
                    mm//=d
            d += 1
        if mm > 1:
            qs.append(mm)
        for q in qs:
            if pow(g, order//q, p) == 1:
                return False
        return True
    g = 2
    while not is_primroot(g):
        g += 1
    h = pow(g, order // n, p)  # primitive n-th root
    s = set()
    cur = 1
    for _ in range(n):
        s.add(cur)
        cur = (cur * h) % p
    return s

def bgk_M(n, p):
    """M = #{ u in mu_n : (1+u) mod p in mu_n }.  (-(1+u) in mu_n iff (1+u) in mu_n since -1 in mu_n.)"""
    G = mu_n(n, p)
    cnt = 0
    for u in G:
        if (1 + u) % p in G:
            cnt += 1
    return cnt, G

def additive_energy_E2(G, p):
    """E_2(G) = #{ (a,b,c,d) in G^4 : a+b = c+d } = sum_t r(t)^2, r(t)=#{(a,b):a+b=t}."""
    from collections import Counter
    r = Counter()
    Gl = list(G)
    for a in Gl:
        for b in Gl:
            r[(a+b) % p] += 1
    return sum(v*v for v in r.values())

def fermat_curve_count(n, p):
    """ #{(x,y) in mu_n^2 : 1 + x + y = 0}  i.e. x+y = -1, x,y in mu_n.
        This is the 'Fermat-curve'-flavoured count; note x = u, y = -(1+u) gives
        the same set as BGK (x in mu_n and -(1+x) in mu_n). So this EQUALS M."""
    G = mu_n(n, p)
    cnt = 0
    for x in G:
        if (p - 1 - x) % p in G:  # y = -1 - x
            cnt += 1
    return cnt

def main():
    print("="*92)
    print("BGK MAGNITUDE  M(n,p) = |mu_n cap -(1+mu_n)|   (EXACT, all primes n|p-1 up to cap)")
    print("="*92)
    for n in [8, 16, 32, 64]:
        # primes p with n | p-1, up to a cap. Cap chosen to get a healthy sample.
        cap = 200000 if n <= 16 else (400000 if n == 32 else 900000)
        primes = [p for p in primerange(3, cap) if (p-1) % n == 0]
        Ms = []
        E2s = []
        max_M = 0
        argmax_p = None
        mersenne_primes = []  # primes with M odd  <=> p | 2^n - 1
        distr = {}
        for p in primes:
            M, G = bgk_M(n, p)
            Ms.append(M)
            distr[M] = distr.get(M, 0) + 1
            # sanity: fermat-curve count must equal M
            fc = fermat_curve_count(n, p)
            assert fc == M, f"fermat-curve count {fc} != M {M} at n={n} p={p}"
            # tripleZero = n*M  (we don't recompute the cube, trust the in-tree theorem; verified small below)
            if M > max_M:
                max_M = M; argmax_p = p
            if M % 2 == 1:
                mersenne_primes.append(p)
            E2s.append(additive_energy_E2(G, p))
        nump = len(primes)
        meanM = sum(Ms)/nump if nump else 0
        # E_2 connection: char-0 clean value is 3n^2 - 3n (even n). measure deviation.
        cleanE2 = 3*n*n - 3*n
        anomalies = sum(1 for e in E2s if e != cleanE2)
        print(f"\n--- n = {n}  (sqrt(n) = {n**0.5:.3f}) : {nump} primes p<{cap} with n|p-1 ---")
        print(f"  M distribution (value:count): "
              + ", ".join(f"{k}:{v}" for k,v in sorted(distr.items())))
        print(f"  mean M = {meanM:.4f},  max M = {max_M} at p={argmax_p}  "
              f"(max/sqrt(n) = {max_M/(n**0.5):.3f}, max/n = {max_M/n:.3f})")
        print(f"  #primes with M odd (p | 2^n-1, Mersenne/Fermat-bad) = {len(mersenne_primes)}"
              + (f" -> {mersenne_primes[:8]}" if mersenne_primes else ""))
        print(f"  E_2 clean (char-0, =3n^2-3n) = {cleanE2}; "
              f"#primes with E_2 != clean (anomaly) = {anomalies} / {nump}")
        # verify E_2 = clean + (extra from BGK)? measure relation E_2 - cleanE2 vs M
        # For a clean smooth subgroup, E_2 = 3n^2-3n exactly (memory fact). Anomaly when additive
        # coincidences (M>0) appear. Tabulate E_2-cleanE2 grouped by M.
        from collections import defaultdict
        byM = defaultdict(list)
        for M_, e_ in zip(Ms, E2s):
            byM[M_].append(e_ - cleanE2)
        print("  E_2 - clean   grouped by M (M -> sorted distinct deltas):")
        for k in sorted(byM):
            ds = sorted(set(byM[k]))
            print(f"      M={k:3d}: deltaE2 in {ds[:10]}")
    print("\n" + "="*92)
    print("verify tripleZero = n*M on a couple of small instances (exact cube enumeration):")
    for (n,p) in [(8,17),(8,41),(16,17),(16,97)]:
        if (p-1)%n: continue
        G = mu_n(n,p); Gl=list(G)
        tz = sum(1 for x in Gl for y in Gl for z in Gl if (x+y+z)%p==0)
        M,_ = bgk_M(n,p)
        print(f"   n={n} p={p}: tripleZero={tz}, n*M={n*M}  match={tz==n*M}")

if __name__ == "__main__":
    main()
