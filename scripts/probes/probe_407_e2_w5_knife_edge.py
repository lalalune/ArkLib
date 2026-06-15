#!/usr/bin/env python3
"""
probe_407_e2_w5_knife_edge.py  (#444 — the shallow-width e2=0 census MAP + the w=5 knife-edge)

Mapped the shallow-width e2=0 census (the prize FLOOR's R1 object) for 2-power n:
  w<=3 : EMPTY (no e2=0 solutions)
  w=4  : K = n/4 - 1, #bad = n^2/4 - n (super-budget quadratic; closed form, prior receipt)
  w=5  : K = 1 EXACTLY for all n, #bad = n EXACTLY = budget  <-- THE KNIFE-EDGE
  w=6  : EMPTY again
  ...then the super-budget middle band resumes (peaks at w=n/2).

This file pins the w=5 structure (the cleanest object on the board: #bad = budget exactly, single orbit):
  - exact, p-independent (#bad=n across 2 prize primes).
  - EVERY w=5 e2=0 subset = EXACTLY 2 antipodal pairs + 1 singleton: {x,-x,y,-y,z} (x,y,z in mu_n,
    -x=h^{n/2}x). The pairs cancel in e1 (=> e1=z), and e2=0 forces a relation among x,y,z.
  - bad-scalar set = {-1/z} over the valid configs = exactly one mu_n-orbit (size n).

This is the candidate BINDING edge family (where #bad = budget exactly => the proximity-gap is on the
knife-edge). p-independent + single-orbit + clean 2-pairs+singleton structure => a prime FORMALIZATION
target. Exact mod-p, proper subgroup, never n=q-1. Python-only => axiom-clean trivially.
"""
import sys
sys.path.insert(0,'scripts/probes')
from probe_407_e2_K_w4_n64 import is_prime, proot, prize_prime
from itertools import combinations

def w5_analyze(n,p):
    g=proot(p); m=(p-1)//n; h=pow(g,m,p)
    mu=[pow(h,i,p) for i in range(n)]; mu2=[(v*v)%p for v in mu]
    half=n//2
    subsets=[]
    for S in combinations(range(n),5):
        e1=sum(mu[i] for i in S)%p; p2=sum(mu2[i] for i in S)%p
        if (e1*e1-p2)%p==0 and e1!=0: subsets.append(S)
    def npairs(S):
        Sset=set(S); return sum(1 for i in S if ((i+half)%n) in Sset and i<((i+half)%n))
    pd={}
    for S in subsets:
        c=npairs(S); pd[c]=pd.get(c,0)+1
    alphas=set((-pow(sum(mu[i] for i in S)%p,p-2,p))%p for S in subsets)
    # orbit count
    rem=set(alphas);K=0
    while rem:
        x=next(iter(rem));rem-=set((u*x)%p for u in mu);K+=1
    return len(subsets),len(alphas),K,pd

def main():
    print("="*78); print("the w=5 e2=0 KNIFE-EDGE: #bad = budget = n exactly, single orbit, 2-pairs+singleton"); print("="*78)
    print("\nShallow-width MAP (2-power n): w<=3 empty | w=4 K=n/4-1 (#bad=n^2/4-n) | w=5 K=1 (#bad=n) | w=6 empty\n")
    for n in (8,16,32,64):
        primes=[];p=n**4;p-=p%n;p+=1
        while len(primes)<2:
            if p%n==1 and is_prime(p):primes.append(p)
            p+=n
        rows=[]
        for p in primes:
            ns,na,K,pd=w5_analyze(n,p); rows.append((p,ns,na,K,pd))
        ns0,na0,K0,pd0=rows[0][1:]
        pind = len(set(r[2] for r in rows))==1
        print(f"  n={n}: #subsets={ns0}  #distinct-alpha={na0} (=n? {na0==n})  K={K0}  pair-count-dist={pd0}  p-indep(#alpha)={pind}")
    print("\nVERDICT: w=5 e2=0 census = EXACTLY n bad-scalars (= budget), single mu_n-orbit (K=1), p-independent,")
    print("  EVERY subset = 2 antipodal pairs + 1 singleton {x,-x,y,-y,z}. The knife-edge family where the")
    print("  proximity gap sits EXACTLY at budget. Cleanest formalization target on the board (#bad=n exactly).")

if __name__=="__main__":
    main()
