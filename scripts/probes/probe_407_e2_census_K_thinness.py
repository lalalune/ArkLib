#!/usr/bin/env python3
"""
probe_407_e2_census_K_thinness.py  (#444 — the load-bearing e2=0 census R1 lane)

CONTEXT (the live prize skeleton, in-tree):
  DeltaStarEqEdge.lean reduces the FLOOR to ONE open hypothesis (R1, `hgood`): the e2=0 over-determined
  locus is the BINDING worst-case bad-scalar family at the window edge, with bad-count = char-0 value.
  _E2DilationDirectCount.lean reduces that count EXACTLY to  #{bad alpha} = n * K(n), where
  K(n) = #{ dilation-orbits (under mu_n) of e1(S)-values over the locus {S subset mu_n, |S|=w=n/2,
  e2(S)=0, e1(S)!=0} }.  Measured in-tree: K = 1, 3, 38 at n = 8, 16, 32  (#bad = n*K).
  K(n) IS the open extremal census (additive-energy twin). The floor closes iff n*K stays within budget.

UNCONTESTED EDGE (no live worker, no report): is K(n) THINNESS-ESSENTIAL (rule-3)?
  Compare the e2=0 census on the SMOOTH subgroup mu_n vs a RANDOM domain D of the same size n, at the
  SAME prime, same width w=n/2.  (For random D the dilation group is mu_n still? NO — the random domain
  has no subgroup self-action.  So for the random control we count the RAW bad-set size #bad_rand and,
  to compare orbit-census apples-to-apples, also the n-quotient #bad_rand / n where meaningful.)
  Cleanest invariant comparison: the RAW e2=0 bad-scalar SET SIZE #{distinct alpha = -1/e1(S)} for
  smooth vs random.  If smooth #bad << random #bad => mu_n SUPPRESSES the e2=0 census (thinness-essential,
  RIGHT direction for the floor: the smooth subgroup has fewer e2=0 negation-pairs).  If smooth >= random
  => anti-helpful (like the LD-radius plateau).

METHOD (exact, proper subgroup, prize prime p~n^4, never n=q-1):
  n in {8,16}, w=n/2.  Smooth mu_n vs 11 random non-subgroup domains of size n.  Exact e2=0 enumeration
  over all C(n,w) w-subsets (feasible n<=16: C(16,8)=12870).  Report #distinct-alpha (the raw census)
  smooth vs random distribution + the subgroup K (orbit count).  n=32 quoted from in-tree (K=38) for the
  growth law; thinness gate run exactly at n=8,16.
Python-only exact => axiom-clean trivially.
"""
import itertools, sys, random
from itertools import combinations

def is_prime(x):
    if x<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x%q==0: return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y=pow(a,d,x)
        if y==1 or y==x-1: continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True;break
        if not ok: return False
    return True

def factor(x):
    f=[];d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:f.append(x)
    return f

def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 0

def prize_prime(n,beta=4):
    p=n**beta
    p-= p%n; p+=1
    while True:
        if p%n==1 and is_prime(p): return p
        p+=n

def e2_census(dom, w, p):
    """exact: over all w-subsets S of dom, find {alpha = -1/e1(S) : e2(S)=0, e1(S)!=0}. return set of alpha."""
    n=len(dom)
    alphas=set()
    nbadsets=0
    for S in combinations(range(n), w):
        e1=0; p2=0
        for i in S:
            v=dom[i]; e1=(e1+v)%p; p2=(p2+v*v)%p
        # e2 = (e1^2 - p2)/2 ; e2=0 <=> e1^2 == p2
        if (e1*e1 - p2)%p==0 and e1%p!=0:
            nbadsets+=1
            alphas.add((-pow(e1,p-2,p))%p)
    return alphas, nbadsets

def orbit_count(alphas, mu, p):
    rem=set(alphas); K=0
    muset=mu
    while rem:
        x=next(iter(rem))
        rem -= set((u*x)%p for u in muset)
        K+=1
    return K

def main():
    print("="*78)
    print("e2=0 census K(n) thinness gate — smooth mu_n vs random domain, exact, prize prime")
    print("="*78)
    random.seed(20260615)
    for n in (8,16):
        p=prize_prime(n,4)
        g=proot(p); m=(p-1)//n; h=pow(g,m,p)
        assert pow(h,n,p)==1 and pow(h,n//2,p)!=1
        mu=[pow(h,i,p) for i in range(n)]
        w=n//2
        # smooth
        a_s, nbs = e2_census(mu, w, p)
        K = orbit_count(a_s, mu, p)
        # random control: 11 draws, raw census size
        rand_dist=[]
        for _ in range(11):
            while True:
                dr=random.sample(range(1,p), n)
                sset=set(dr)
                if not all((x*y%p) in sset for x in dr[:3] for y in dr[:3]): break
            a_r,_=e2_census(dr, w, p)
            rand_dist.append(len(a_r))
        rmin,rmax=min(rand_dist),max(rand_dist)
        rmed=sorted(rand_dist)[len(rand_dist)//2]
        print(f"\n--- n={n} w={w} p={p} (beta4, index m={m}) ---")
        print(f"    SMOOTH mu_n: #e2=0 bad-sets={nbs}  #distinct-alpha={len(a_s)}  K(orbits)={K}  (n*K={n*K}, #bad=n*K? {len(a_s)==n*K})")
        print(f"    RANDOM dom : #distinct-alpha over 11 draws: min={rmin} med={rmed} max={rmax}  dist={sorted(rand_dist)}")
        sa=len(a_s)
        if sa < rmin:
            v=f"SMOOTH census ({sa}) BELOW all random [{rmin},{rmax}] => mu_n SUPPRESSES the e2=0 census (THINNESS-ESSENTIAL, RIGHT direction for the floor — LIVE lever for R1)"
        elif sa > rmax:
            v=f"SMOOTH census ({sa}) ABOVE all random => mu_n INFLATES it (anti-helpful, like the even-moment profile)"
        else:
            v=f"SMOOTH census ({sa}) INSIDE random [{rmin},{rmax}] => NOT thinness-separated (e2=0 census is domain-generic; R1 floor would be non-thinness-essential)"
        print(f"    VERDICT: {v}")
    print(f"\n(in-tree reference for the growth law: K = 1, 3, 38 at n=8,16,32; #bad = n*K)")

if __name__=="__main__":
    main()
