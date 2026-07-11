#!/usr/bin/env python3
"""
PROBE v3 (the FRONTIER question): does per-gamma multiplicity of aligned a-sets
GROW with band depth a? Prize window = DEEP band a ~ n/2. If at deep band each bad
gamma owns MANY aligned a-sets while #bad stays small, the census bound #bad <=
#alignedSets is exponentially LOOSE precisely at the prize window -- a structural
reason the crude packing budget (#alignedSets ~ C(2N,r)) overflows at r~n/2 while
the TRUE #bad stays within budget. This is the distinct-gamma vs incidence gap.

Mechanism predicted by Aligned.mono: if gamma owns a LARGE aligned set S0 (card s),
then EVERY a-subset of S0 (a<=s) is also gamma-aligned. So mult(gamma) at band a
>= C(s, a) where s = max aligned-set size for gamma = the AGREEMENT (list) radius.
=> mult(gamma) at band a = C(agree(gamma), a) -- combinatorially explicit!
We verify: sweep band a from k+1 up, track #alignedSets, #bad, and whether
mult(gamma) == C(maxAgreeSet(gamma), a).
"""
import itertools
from collections import defaultdict
from math import comb

def setup(a, beta=4):
    n=2**a; p=n**beta+1
    while True:
        p+=1
        if (p-1)%n: continue
        if all(p%d for d in range(2,int(p**0.5)+1)): break
    for c in range(2,p):
        o=1;y=c%p
        while y!=1: y=(y*c)%p;o+=1
        if o==p-1: g=c;break
    h=pow(g,(p-1)//n,p)
    return p,n,[pow(h,i,p) for i in range(n)]

def inv(x,p): return pow(x%p,p-2,p)
def divdiff(t,u,dom,p):
    s=0
    for b in range(len(t)):
        d=1;pb=dom[t[b]]
        for c in range(len(t)):
            if c!=b: d=(d*(pb-dom[t[c]]))%p
        s=(s+u[t[b]]*inv(d,p))%p
    return s

def agree_sets_for_gamma(gamma, u0,u1,dom,n,k,p):
    """For fixed gamma, w=u0+gamma*u1. Find the MAX-size sets on which w agrees with
    deg<k poly (= max aligned set). A point i 'fits' a set if w on that set is deg<k.
    Equivalent: maximal S with all (k+1)-subsets having res(w)=0."""
    w=[(u0[i]+gamma*u1[i])%p for i in range(n)]
    # which (k+1)-subsets t have res(w,t)=0?
    good=set()
    for t in itertools.combinations(range(n),k+1):
        if divdiff(t,w,dom,p)==0: good.add(t)
    # an aligned set = set whose every (k+1)-subset is in 'good'. Max such = max clique
    # in the (k+1)-uniform "agreement hypergraph". For small n brute: largest S s.t.
    # all C(|S|,k+1) subsets good.
    best=k
    for sz in range(n, k, -1):
        found=False
        for S in itertools.combinations(range(n),sz):
            if all(t in good for t in itertools.combinations(S,k+1)):
                found=True;break
        if found: best=sz;break
    return best

def probe(a_exp,k,A,B,beta=4):
    p,n,dom=setup(a_exp,beta)
    u0=[pow(dom[i],A,p) for i in range(n)]
    u1=[pow(dom[i],B,p) for i in range(n)]
    print(f"\n== n={n} k={k} (A,B)=({A},{B}) p={p} ==")
    # full census per band
    for band in range(k+1, min(n, k+5)+1):
        owner=defaultdict(int); total=0
        for S in itertools.combinations(range(n),band):
            gam=None;ok=True;nd=False
            for t in itertools.combinations(S,k+1):
                D0=divdiff(t,u0,dom,p);D1=divdiff(t,u1,dom,p)
                if D0 or D1: nd=True
                if D1==0:
                    if D0: ok=False;break
                    continue
                gt=(-D0*inv(D1,p))%p
                if gam is None: gam=gt
                elif gam!=gt: ok=False;break
            if ok and nd and gam is not None:
                total+=1;owner[gam]+=1
        mults=sorted(owner.values(),reverse=True)
        # predicted mult = C(agree(gamma), band) for each bad gamma
        pred=None
        if owner:
            g0=max(owner,key=owner.get)
            s0=agree_sets_for_gamma(g0,u0,u1,dom,n,k,p)
            pred=(s0, comb(s0,band), owner[g0])
        print(f"  band={band}: #alignedSets={total} #bad={len(owner)} gap={total-len(owner)} "
              f"maxmult={mults[0] if mults else 0} pred[s0,C(s0,band),actual]={pred}")

if __name__=="__main__":
    probe(3,2,3,4)
    probe(4,2,5,7)
