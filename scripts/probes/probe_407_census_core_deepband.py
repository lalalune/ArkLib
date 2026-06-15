#!/usr/bin/env python3
"""
probe_407_census_core_deepband.py  (#407 / #371 census-vs-CORE lane, DEEP-BAND)

Follow-up to probe_407_census_core_equivalence.py. The boundary band a=k+1 is DEGENERATE
(#alignable = C(n,k+1) = ALL sets, since any k+1 points have one tuple = one ratio trivially).
The census's discriminating content -- and the band the WELD (CensusDominationWeld.lean) actually
binds at (a >= rm+1, DEEP interior) -- is a > k+1, where a set must have MANY (k+1)-subtuples ALL
sharing ONE ratio (a real alignment constraint). This probe measures #alignable / #bad at the DEEP
bands and adds the thinness control (rule 3).

OBJECT (same as the equivalence probe): mu_n = <g> proper subgroup of F_p*, smooth n=2^mu, prize p.
far line u0=x^k, u1=x^{k+1}. a-set alignable iff ALL nondeg (k+1)-subtuples share one gamma=-e0/e1.
(U) proven in-tree: #bad <= #alignable. Equivalence to CORE needs the reverse tight at the BINDING band.

We report, per deep band a:  #alignable, #bad(=distinct gammas), ratio, and #alignable/C(n,a) (the
SUPPLY FRACTION -- how the alignable supply DECAYS with depth; the deployed threshold radius = deepest
band with supply > eps*p). The binding band is the deepest a with #alignable > 0.

THINNESS CONTROL: run the SAME k,a on a THICK subgroup (n | p-1 with n NOT a 2-power, e.g. n=12,
mu_n order 12) and compare the supply-decay + ratio. If the census<->CORE GAP (ratio) is thinness-
INVARIANT, the census route's faithfulness does not depend on the 2-power structure CORE needs (rule 3
relevance). Probe-first, exact mod-p, proper subgroup, never n=q-1.
"""
import itertools, sys
from math import comb

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def prize_prime(n, beta=4.0):
    p = int(n**beta); p += (1 - p) % n
    while not (isprime(p) and (p-1) % n == 0):
        p += n
    return p

def find_g(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in _prime_factors(n)):
            return x
    raise ValueError

def _prime_factors(n):
    f=set(); d=2; m=n
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def divided_diff(idxs, uvals, xs, p):
    total = 0
    for i in idxs:
        den = 1
        for j in idxs:
            if i == j: continue
            den = (den * ((xs[i]-xs[j]) % p)) % p
        total = (total + uvals[i]*pow(den, p-2, p)) % p
    return total

def census_band(n, p, g, A, B, k, a):
    xs = [pow(g,i,p) for i in range(n)]
    u0 = [pow(xx,A,p) for xx in xs]; u1 = [pow(xx,B,p) for xx in xs]
    alignable=0; bad=set()
    for S in itertools.combinations(range(n), a):
        gamma=None; ok=True; nd=False
        for T in itertools.combinations(S,k+1):
            e0=divided_diff(T,u0,xs,p); e1=divided_diff(T,u1,xs,p)
            if e1==0:
                if e0!=0: ok=False; break
                continue
            nd=True
            gT=(-e0*pow(e1,p-2,p))%p
            if gamma is None: gamma=gT
            elif gamma!=gT: ok=False; break
        if ok and nd and gamma is not None:
            alignable+=1; bad.add(gamma)
    return alignable, len(bad)

def run_domain(label, n, p, g, k):
    A,B = k, k+1
    print(f"\n## {label}: n={n} p={p} k={k} (far line x^{A}+gamma x^{B})")
    print(f"{'a':>3} {'C(n,a)':>9} {'#align':>8} {'supplyFrac':>11} {'#bad':>6} {'ratio(al/bad)':>13} {'binding?':>9}")
    print("-"*68)
    deepest=None
    for a in range(k+1, n):
        al, bad = census_band(n,p,g,A,B,k,a)
        cna = comb(n,a)
        sf = al/cna if cna else 0.0
        ratio = al/bad if bad else float('inf')
        binding = ""
        if al>0:
            deepest=a
        if al==0 and deepest is not None:
            print(f"{a:>3} {cna:>9} {al:>8} {sf:>11.4f} {0:>6} {'--':>13} (supply exhausted above a={deepest})")
            break
        print(f"{a:>3} {cna:>9} {al:>8} {sf:>11.4f} {bad:>6} {ratio:>13.2f}")
    return deepest

def main():
    print("# DEEP-BAND census-vs-CORE: #alignable supply decay + ratio to #bad, smooth vs thick (#407/#371)")
    # SMOOTH prize domain
    for n,k,beta in [(16,2,4.0),(16,4,4.0),(8,2,4.0)]:
        p=prize_prime(n,beta); g=find_g(p,n)
        run_domain(f"SMOOTH 2^{n.bit_length()-1}", n, p, g, k)
    # THICK control: n=12 (=4*3, NOT a 2-power), same k -- rule-3 thinness comparison
    for n,k,beta in [(12,2,4.0),(12,4,4.0)]:
        p=prize_prime(n,beta); g=find_g(p,n)
        run_domain(f"THICK n={n}(non-2pow)", n, p, g, k)
    print("\n# READ:")
    print("# - supplyFrac decay = how the alignable supply thins with band depth (deployed radius = deepest a w/ supply>eps*p).")
    print("# - ratio al/bad at the DEEPEST (binding) band is the census<->CORE faithfulness at the band the weld uses.")
    print("# - smooth vs thick: if the binding-band ratio is thinness-INVARIANT, census faithfulness is not 2-power-essential.")

if __name__=='__main__':
    main()
