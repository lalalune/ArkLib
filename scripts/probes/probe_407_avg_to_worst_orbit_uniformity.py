#!/usr/bin/env python3
"""
#407 ROUTE: AVERAGE -> WORST via Galois/coset/orbit uniformity of the EXACT far-line incidence
I(a,b;r) (FarCosetExplosion.epsMCA_ge_far_incidence; the in-tree exact, p-independent delta* count).

VERDICT (reproducible, exact, p-independent across 2 primes): the route DOES NOT close the gap.
  (1) The genuine across-DIRECTION symmetry is the Frobenius exponent action a->a*(p mod n).
      In the prize regime mu_n subset F_q FORCES n | (q-1); for a prime field p == 1 mod n, so
      the exponent-Galois subgroup <p mod n> = {1} is TRIVIAL at EVERY n (checked n=8..4096).
  (2) Hence the worst direction sits in a Galois orbit of SIZE 1 (a SINGLETON) -- measured at
      n=8 (r=3,4,5) and structurally for all n. There is no large orbit whose average is forced
      up by the worst.
  (3) At the binding rung (n=8, r=4, delta=0.5) avg(I)=2.86 < 8=budget BUT max(I)=9 > 8=budget:
      the average certifies GOOD while the worst is BAD. The average-to-worst gap is exactly the
      thing that decides delta*, and it is OPEN (gap ratio max/avg = 3.15 there, 12 at r=3).
  (4) The per-line dilation symmetry (ActionOrbitFRI.agreement_orbit_invariance) acts on the line
      parameter alpha INSIDE one direction's count (making the bad-alpha set orbit-closed), NOT
      across directions; "#orbits = O(1)" is then CIRCULAR with "#bad = O(n)" (the floor itself).
  (5) The PERIOD-side mirror is already an axiom-clean Lean no-go: the periods are EXCHANGEABLE
      white-noise (one linear constraint), max ~ iid-Gumbel = average + sqrt(2 log #freq) spread;
      Frontier/_MetaTheoremSecondOrderFloor.secondMoment_method_floor proves any second-moment
      (=average/Parseval) method is sqrt(S)-lossy via the SPIKE family (cannot tell flat from spike).

So algebraic uniformity is NOT strong enough to collapse average to worst: the only group that
relates distinct directions is the Frobenius exponent action, which is trivial in the prize regime.
Reuses incidence() from probe_farline_incidence_exact.py.
"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.getcwd(), 'scripts', 'probes'))
from prize_workspace import get_W
from probe_farline_incidence_exact import find_prime_cong1, incidence

def galois_exp_multipliers(n, p):
    g = p % n; sub = {1}; cur = g % n
    while cur not in sub:
        sub.add(cur); cur = (cur*g) % n
    return sub

def galois_orbit(n, a, b, mults):
    return frozenset(((a*e)%n,(b*e)%n) for e in mults)

def analyze(n,k,r,p):
    S=list(get_W(n,p).S); size=n-r
    dirs=[(a,b) for b in range(k,size) for a in range(n) if a!=b]
    if not dirs: return None
    Iv={}
    for (a,b) in dirs:
        c,sat=incidence(S,p,k,a,b,r); Iv[(a,b)]=p if sat else c
    vals=list(Iv.values()); avg=sum(vals)/len(vals); mx=max(vals)
    gal=galois_exp_multipliers(n,p)
    worst=[d for d,v in Iv.items() if v==mx]
    w=worst[0]; worb=galois_orbit(n,w[0],w[1],gal)&set(Iv.keys())
    worb_ivs=set(Iv[x] for x in worb)
    return dict(delta=r/n,nd=len(Iv),avg=avg,mx=mx,gap=mx/avg if avg else 0,
                gal=len(gal),wsz=len(worb),wconst=len(worb_ivs)<=1,nw=len(worst),
                avgle=avg<=n,mxle=mx<=n)

def main(plan):
    print("== AVG->WORST via Galois/orbit uniformity of EXACT far-line incidence I(a,b;r); budget=n ==",flush=True)
    for (n,k,rs) in plan:
        for plo in (200003,500003):
            p=find_prime_cong1(n,plo); gal=galois_exp_multipliers(n,p)
            print(f"-- n={n} k={k} rho={k/n:.3f} p={p} (Frobenius exp-subgrp |<p mod n>|={len(gal)}) --",flush=True)
            for r in rs:
                res=analyze(n,k,r,p)
                if res is None: continue
                print(f"   r={r} d={res['delta']:.4f}: avg={res['avg']:.2f} max={res['mx']} "
                      f"gap=max/avg={res['gap']:.2f} | worst-Galois-orbit-size={res['wsz']} "
                      f"I-const-on-orbit={res['wconst']} #worst-dirs={res['nw']} "
                      f"| avg<=n:{res['avgle']} max<=n:{res['mxle']}",flush=True)
            print(flush=True)

if __name__=='__main__':
    main([(8,2,range(3,6)),(16,4,(8,9,10))])
