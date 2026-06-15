#!/usr/bin/env python3
"""
probe_407_e2_census_mechanism.py  (#444 — sharpen the e2=0 census thinness finding, rule-6)

The thinness gate found: smooth mu_n has n*K e2=0 bad-sets (8,48 at n=8,16) but RANDOM domains have ZERO.
RULE-6 worry: random=0 could be a DENSITY artifact (e2(S)=0 is one equation mod p; #subsets C(n,w) ~ 12870
<< p ~ 65537, so random subsets generically miss it). Need to separate "structural (subgroup forces e2=0)"
from "density (random just too sparse to hit a codim-1 condition)".

TESTS:
 (A) Is the smooth e2=0 locus the ANTIPODAL structure? In mu_n (n even) the map x -> -x = h^{n/2} x is a
     fixed-point-free involution on mu_n (since -1 = h^{n/2} in mu_n). A subset S closed under x->-x has
     e1(S)=0 (pairs cancel) -> but we need e1!=0. Test: characterize WHICH w-subsets give e2=0 & e1!=0.
     Hypothesis: e2(S)=0 forces a specific near-antipodal balance the subgroup supplies but random can't.
 (B) DENSITY CONTROL: for random, instead of full random domain, count e2=0 over a MATCHED-density model:
     does a random domain EVER produce e2=0 at this subset-count? Estimate expected hits = C(n,w)/p and
     compare. If subgroup hits >> expected-random AND the expected-random ~ C(n,w)/p ~ 0.2-1, then the
     subgroup EXCESS over the density baseline is the structural signal.
 (C) Confirm the smooth count is p-INDEPENDENT (char-0 structural) across 2 prize primes — if so, it is a
     genuine cyclotomic count, NOT a mod-p accident => structurally real, not density-random.

Exact, proper mu_n, prize primes, never n=q-1. Python-only => axiom-clean trivially.
"""
import itertools, math
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
def prize_primes(n,beta,cnt=2):
    p=n**beta; p-=p%n; p+=1; out=[]
    while len(out)<cnt:
        if p%n==1 and is_prime(p): out.append(p)
        p+=n
    return out

def e2zero_subsets(dom,w,p):
    n=len(dom); res=[]
    for S in combinations(range(n),w):
        e1=0;p2=0
        for i in S: v=dom[i]; e1=(e1+v)%p; p2=(p2+v*v)%p
        if (e1*e1-p2)%p==0 and e1%p!=0: res.append(S)
    return res

def main():
    print("="*78); print("e2=0 census MECHANISM — antipodal? density? p-independent? (rule-6 sharpening)"); print("="*78)
    for n in (8,16):
        w=n//2
        primes=prize_primes(n,4,2)
        counts=[]
        antip_frac=None
        for p in primes:
            g=proot(p); m=(p-1)//n; h=pow(g,m,p)
            mu=[pow(h,i,p) for i in range(n)]
            neg = h**(n//2) % p  # = -1 in mu_n
            assert (neg* 1 - (p-1))%p==0, f"h^(n/2) should be -1, got {neg} vs {p-1}"
            ss = e2zero_subsets(mu,w,p)
            counts.append(len(ss))
            if antip_frac is None:
                # (A) how many of these subsets are closed under index i -> i+n/2 (the x->-x involution)?
                half=n//2
                def is_antip_closed(S):
                    Sset=set(S)
                    return all(((i+half)%n) in Sset for i in S)
                n_antip=sum(1 for S in ss if is_antip_closed(S))
                # also: paired structure - count subsets containing >=1 antipodal pair
                def has_pair(S):
                    Sset=set(S)
                    return any(((i+half)%n) in Sset for i in S)
                n_haspair=sum(1 for S in ss if has_pair(S))
                antip_frac=(n_antip,n_haspair,len(ss))
        cdens = math.comb(n,w)/primes[0]
        pind = len(set(counts))==1
        print(f"\n--- n={n} w={w} primes={primes} ---")
        print(f"    smooth #e2=0 subsets across primes: {list(zip(primes,counts))}  p-INDEPENDENT={pind}")
        print(f"    (A) of {antip_frac[2]} e2=0 subsets: antipodal-CLOSED={antip_frac[0]}, contains>=1 antipodal pair={antip_frac[1]}")
        print(f"    (B) density baseline expected random hits = C({n},{w})/p = {cdens:.3f}  (vs smooth {counts[0]})")
        excess = counts[0]-cdens
        print(f"        => smooth EXCESS over density baseline = {excess:.2f}  ({'STRUCTURAL' if excess>2 else 'within density noise'})")
        print(f"    (C) p-independent (char-0 structural) = {pind}  => {'genuine cyclotomic count, not mod-p accident' if pind else 'p-dependent, suspect'}")

if __name__=="__main__":
    main()
