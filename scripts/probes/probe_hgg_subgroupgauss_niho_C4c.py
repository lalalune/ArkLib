#!/usr/bin/env python3
"""
probe_hgg_subgroupgauss_niho_C4c.py  (#407 char-p wall, C4 closing test)

The ONE genuine HGG<->Gauss-period bridge: the cross-correlation spectrum of certain decimations
(Niho, and the index-m subgroup decimations of Baumert-McEliece-Mykkeltveit type) is EXACTLY
expressed via GAUSS PERIODS of small index. e.g. the 4-valued / few-valued cross-correlation of
m-sequences with decimation d s.t. gcd(d, p^e-1)=index INVOLVES eta-periods of that index.

HGG's THEOREMS in that tradition come in two flavors:
  (a) FEW-VALUED (index r small, r=2,3,4,5,6): the spectrum is explicitly computed, finitely many
      values, each O(sqrt field). These EXIST and give upper bounds -- but ONLY for small index r,
      i.e. mu_n with n = (p^e-1)/r and r=O(1) small  =>  n ~ p^e/r ~ FULL group (n=p-1 forbidden!).
  (b) LARGE index (the prize: n=2^mu thin, m=(p-1)/n LARGE, so index r = n is LARGE): the spectrum
      is MANY-valued and HGG gives NO closed few-valued bound -- it becomes the open Gauss-sum problem.

This probe makes the dichotomy QUANTITATIVE: for the prize, which subgroup is "thin"?
The HGG few-valued results control eta over mu_N where N = (p-1)/r, r = SMALL index.
The prize needs eta over mu_n, n = SMALL (2^mu), i.e. index r = (p-1)/n = m = LARGE.
These are OPPOSITE ends. We measure: as the subgroup INDEX r grows from small (HGG regime) to
large (prize regime), the spectrum goes from few-valued (bounded, ~sqrt) to many-valued (the wall).
"""
import math
from cmath import exp, pi
from collections import Counter

def is_prime(x):
    if x<2: return False
    if x%2==0: return x==2
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def primroot(p):
    phi=p-1; mm=phi; facs=set(); d=2
    while d*d<=mm:
        if mm%d==0:
            facs.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for gg in range(2,p):
        if all(pow(gg,phi//f,p)!=1 for f in facs): return gg

def periods_over_subgroup_of_order(p, g, N):
    # mu_N : subgroup of order N (N | p-1). index r = (p-1)/N.
    r = (p-1)//N
    gen = pow(g, r, p)
    mu=[]; x=1
    for _ in range(N):
        mu.append(x); x=(x*gen)%p
    w=exp(2j*pi/p)
    etas=[abs(sum(w**((b*xx)%p) for xx in mu)) for b in range(1,p)]
    return etas, r

def main():
    print("="*78)
    print("HGG few-valued (small index r) vs prize (large index r=m): the spectrum dichotomy")
    print("regime: a fixed prime p; vary subgroup order N => index r=(p-1)/N")
    print("HGG few-valued THEOREMS live at SMALL r (period ~ full group). Prize lives at LARGE r.")
    print("="*78)
    # use a prime with many divisors of p-1 so we can scan index r
    # pick p = 1 + (2^7)*M form, want p-1 = 128 * something with small-r divisors
    # p-1 should have divisors giving small index r AND a 2-power subgroup of small order n
    p = 0
    M = 2
    while True:
        cand = 1 + 128*M
        if is_prime(cand):
            p = cand; break
        M += 1
    g = primroot(p)
    pm1 = p-1
    print(f"p = {p}  (p-1 = {pm1} = {pm1})  primitive root g={g}\n")
    print(f"{'index r':>8} | {'N=ord(mu)':>10} | {'#distinct |eta|':>16} | {'max|eta|':>9} | {'sqrt(N)':>8} | {'max/sqrtN':>9}")
    print("-"*78)
    # divisors of p-1, choose a ladder of indices from small to large
    divs = sorted(d for d in range(1, pm1+1) if pm1 % d == 0)
    # index r ranges over divisors; we want r small (HGG) ... r large (prize, N=2^mu small)
    sample_r = [d for d in divs if d in (2,3,4,5,6,8) or d >= pm1//64]
    sample_r = sorted(set(sample_r))
    for r in sample_r:
        N = pm1 // r
        if N < 2 or N > 4000:   # keep cost sane; prize end is small N
            continue
        etas, rr = periods_over_subgroup_of_order(p, g, N)
        nd = len(Counter(round(a,3) for a in etas))
        mx = max(etas)
        sq = math.sqrt(N)
        tag = ""
        if r <= 6: tag = "  <- HGG few-valued regime (small index)"
        if N <= 64 and (N & (N-1))==0: tag = "  <- PRIZE regime (n=2^mu, large index)"
        print(f"{r:>8} | {N:>10} | {nd:>16} | {mx:>9.3f} | {sq:>8.3f} | {mx/sq:>9.3f}{tag}")
    print("\n" + "="*78)
    print("READING:")
    print(" - SMALL index r (2..6): #distinct |eta| is small (few-valued), max ~ small*sqrt -- this")
    print("   is the HGG/Baumert-McEliece regime where exact spectra & upper bounds EXIST. But here")
    print("   N ~ (p-1)/r is HUGE (nearly the full group) -- NOT a thin prize subgroup.")
    print(" - LARGE index r (prize: N=2^mu small): #distinct |eta| EXPLODES (many-valued), max/sqrtN")
    print("   GROWS -- HGG few-valued theorems do NOT cover this; it is the open Gauss-sum wall.")
    print(" The HGG tradition controls the WRONG end of the index axis for the prize.")
    print("="*78)

if __name__ == "__main__":
    main()
