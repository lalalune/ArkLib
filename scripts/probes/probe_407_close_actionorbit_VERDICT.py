#!/usr/bin/env python3
"""
#407 LANE D (Action-Orbit, Chai-Fan 2026/861) -- CONSOLIDATED VERDICT on the OPEN ITEM.

OPEN ITEM (verbatim): "attack Q1 (norm non-vanishing, d>=16 OPEN; d in {4,8} settled). TEST Q1
for d=16,32 over prize-scale fields -- does the norm vanish (refutes) or not? Determine whether
Action-Orbit gives a genuine O(1)/|F| on PLAIN RS over mu_n in the window interior, or collapses
to BGK."

PROVENANCE WARNING (load-bearing): the actual paper eprint 2026/861 is Cloudflare-blocked; the
local copies (~/papers/arklib/2026_861.pdf, /tmp/2026_861.pdf) are BOTH "Just a moment..." HTML,
NOT the PDF. So the precise statement of "Q1 / Conjecture 4.12 / the norm Norm_{K_d/Q}(F_d)" is
RECONSTRUCTED from ActionOrbitFRI.lean + the in-tree KB + issue comments, NOT quoted from the
paper. The operative reconstructed form tested here:

  Q1 (route i, the self-similarity hypothesis (*)_d):  on the mu_d-orbit-PRIMITIVE gap stratum
  V_d^prim (an ANTIPODAL-FREE Y in mu_d, p_1(Y)=0),  p_1=0 => p_a=0 for every odd a.
  Equivalent (norm form): Norm_{K_d/Q}(F_d) does NOT vanish on V_d^prim mod p.
  K=O(1) soundness bound holds IFF (*)_d holds for all dyadic d=2^j.  Settled d in {4,8}.

THE COMPUTATION (this campaign, all EXACT unless noted; see sibling probes):
  1. badSet_orbit_closed (ActionOrbitFRI.lean) is correct & axiom-clean: the bad-alpha set IS a
     union of <w^{b-a}>-orbits of size S=n/gcd(b-a,n). VERIFIED on genuine RS (n=8 ground truth,
     orbit-closed=YES). So K = |bad|/S EXACTLY -- orbit compression buys a factor of S and NO MORE.
  2. K=1 ESCAPE <=> V_d^prim empty. Genuine-RS structured (3k/2,2k) bad-rho = {rho^8=16} (one
     orbit, K=1) EXACTLY at d=2,3 (n=16,24, locator method) -- the (*)_d-clean regime.
  3. (*)_d char-p CENSUS over prize-scale fields (p ~ d^4, p=1 mod d), EXACT exhaustive MITM:
       d=8 : V^prim empty (0 primitive pts)            -> (*)_8 holds      [matches "settled"]
       d=16: V^prim empty (0 primitive pts, 4-6 primes) -> (*)_16 holds    [genuinely clean]
       d=32: 192-384 primitive pts, 100% VIOLATE       -> (*)_32 FAILS char-p
       d=64: spurious pts found (sampled), 100% violate -> (*)_d FAILS d>=32
     => the norm Norm_{K_d/Q}(F_d) VANISHES mod every tested prize-scale prime for d>=32.
  4. K-GROWTH (|Sigma_r| value-spectrum proxy): K explodes x19.5 (rho=1/4) / x34 (rho=1/2) per
     n-doubling at fixed window depth -- NOT O(1).

VERDICT (this probe re-derives the d=8/16/32 census line so the file is self-contained):
  * d=16 is genuinely SETTLED but for a reason the "d in {4,8} settled, d>=16 open" framing
    obscures: V_16^prim is EMPTY mod p (no primitive point to violate), so (*)_16 is VACUOUS.
  * d=32 (and 64) the norm VANISHES mod p at prize scale -> Q1 route (i) self-similarity FAILS
    -> the orbit count is NOT O(1) at the prize regime n=2^mu (d=2^mu >= 2^30 >> 32).
  * Therefore Action-Orbit does NOT give O(1)/|F| on plain RS over mu_n in the window interior
    at the prize scale: it delivers K=1 ONLY while V_d^prim is empty (d<=16), and INFLATES once
    the char-p spurious primitive stratum opens (d>=32) -- which is exactly the BGK/sum-product
    regime (short antipodal-free vanishing 2-power-root-of-unity sums mod a poly-norm split
    prime, the SAME object Lam-Leung controls in char-0 and BGK only reaches at n^{1-1/2880}).
    The lane COLLAPSES to BGK at the open boundary, it does not bypass it.
"""
import itertools
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def primes_1_mod_n(n,lo,cap):
    out=[]; p=lo|1
    while len(out)<cap:
        if (p-1)%n==0 and is_prime(p): out.append(p)
        p+=2
    return out

def find_gen(p,n):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//n,p)
        if pow(w,n,p)==1 and all(pow(w,n//q,p)!=1 for q in (2,3,5,7,11,13) if n%q==0):
            return w
    raise RuntimeError

def census_exact(p,d):
    """EXACT count of antipodal-free Y in mu_d with p_1(Y)=0 mod p, and how many violate (*)_d."""
    half=d//2; w=find_gen(p,d); rv=[pow(w,j,p) for j in range(d)]
    odd_a=[a for a in range(3,d,2)]; pairs=list(range(half)); Lh=half//2
    def enum(pp):
        out=[]
        for ch in itertools.product(range(3),repeat=len(pp)):
            s=0; exps=[]
            for t,c in zip(pp,ch):
                if c==1: exps.append(t); s=(s+rv[t])%p
                elif c==2: exps.append(t+half); s=(s+rv[t+half])%p
            out.append((s,tuple(exps)))
        return out
    left=enum(pairs[:Lh]); right=enum(pairs[Lh:])
    rb=defaultdict(list)
    for s,e in right: rb[s].append(e)
    np_=nv=0; ex=None
    for ls,le in left:
        tgt=(-ls)%p
        for re in rb.get(tgt,[]):
            Y=le+re
            if len(Y)<2: continue
            Ys=set(Y)
            if any(((j+half)%d) in Ys for j in Y): continue  # antipodal-free guard
            np_+=1; v=None
            for a in odd_a:
                s=sum(pow(w,(a*j)%d,p) for j in Y)%p
                if s!=0: v=a; break
            if v is not None:
                nv+=1
                if ex is None: ex=(sorted(Y),v)
    return np_,nv,ex

def main():
    print("="*88)
    print("#407 LANE D -- Action-Orbit Q1 VERDICT: (*)_d char-p census, d=8/16/32, prize-scale")
    print("="*88)
    print("Q1 holds at d <=> Norm_{K_d/Q}(F_d) != 0 mod p <=> V_d^prim empty / (*)_d non-violated.\n")
    print(f"  {'d':>3} {'primes':>7} {'primitive_pts':>14} {'violating':>10} {'verdict':>34}")
    for d in [8,16,32]:
        ps=primes_1_mod_n(d, d**4, 4)
        tp=tv=0; ex=None
        for p in ps:
            a,b,e=census_exact(p,d); tp+=a; tv+=b
            if ex is None: ex=e
        if tp==0:
            verdict="(*)_d HOLDS (V^prim empty mod p)"
        elif tv==tp:
            verdict="(*)_d FAILS -- norm VANISHES mod p"
        else:
            verdict=f"(*)_d FAILS {tv}/{tp}"
        print(f"  {d:>3} {len(ps):>7} {tp:>14} {tv:>10} {verdict:>34}")
        if ex and d==32:
            print(f"        d=32 example: antipodal-free Y={ex[0]}, p_1=0 but p_{ex[1]}!=0 (spurious primitive point)")
    print()
    print("CONCLUSION: Q1 SETTLED at d<=16 (V^prim empty); REFUTED at d>=32 (norm vanishes mod p")
    print("at every tested prize-scale prime). Action-Orbit delivers O(1)/|F| ONLY for d<=16; it")
    print("COLLAPSES to the BGK/sum-product wall at d>=32 = the prize regime n=2^mu. No bypass.")

if __name__=="__main__":
    main()
