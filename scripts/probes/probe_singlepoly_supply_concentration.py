#!/usr/bin/env python3
"""#389: does the worst single-polynomial word w=eval(W) over mu_n concentrate its
sub-Johnson supply (#explainable t-cores = sum_c C(agree(c,w),t)) to the random mean
C(n,t)/q^{m+1}?  Sampled over non-codeword single-poly W of effective degree in [k, 2k+m+1].

FINDING (n>d so no X^n-1 reduction degeneracy): the worst single-poly supply is
ROUGHLY q-INDEPENDENT and modest -- e.g. n=8,k=2,m=1: ~6,5,5,2 across q=17,41,73,97;
n=10: ~15-20 -- i.e. ~f(n) << C(n,k) (the provable polyword_supply_le bound) and
>> the random mean ~1/q^{m+1}.  So single-poly words do NOT concentrate to the mean;
the worst case is a q-independent f(n).  This refines the deep-band wall: the open
content is the q-independent worst-case f(n) of the single-poly family, between the
provable C(n,k) and the (unattained) random mean.
"""

# Genuine test: n > d = 2k+m+1 so single-poly words don't reduce to codewords over mu_n.
# Worst NON-codeword single-poly word supply vs random mean. (Excludes W reducing mod
# X^n-1 to degree < k.)
import itertools, random
from math import comb

def prim_root(q):
    for g in range(2,q):
        x=1; ok=True
        for _ in range(q-1):
            x=(x*g)%q
            if x==1 and _<q-2: ok=False; break
        if ok and x==1: return g
    return None

def run(q,n,k,m, samples=3000):
    assert (q-1)%n==0
    g=prim_root(q); h=pow(g,(q-1)//n,q); mu=[pow(h,i,q) for i in range(n)]
    assert len(set(mu))==n
    a=k+m+1; d=2*k+m+1
    assert n>d, f"need n>d={d}"
    def evalpoly(coeffs,x):
        r=0
        for c in reversed(coeffs): r=(r*x+c)%q
        return r
    codewords=list(itertools.product(range(q),repeat=k))
    cw_vals=[[evalpoly(c,x) for x in mu] for c in codewords]
    def reduces_to_codeword(Wc):
        # W mod (X^n-1) as function on mu = W on mu; is it equal to some deg<k codeword?
        Wv=[evalpoly(Wc,x) for x in mu]
        # interpolate deg<n; check if a deg<k poly matches -> via: agree with c=interpolant deg<k?
        # cheaper: W is codeword-equiv iff exists P deg<k with P=W on all mu
        for cv in cw_vals:
            if cv==Wv: return True
        return False
    rand_mean=comb(n,a)/(q**(m+1))
    best=0; bestdesc=None
    random.seed(2)
    cands=[]
    for j in range(k,d+1):
        Wc=[0]*j+[1]; cands.append((Wc,f"X^{j}"))
    for lam in range(1,min(q,5)):
        Wc=[0]*a+[1];
        if a-2>=0: Wc[a-2]=lam
        cands.append((Wc,f"X^{a}+{lam}X^{a-2}"))
    for _ in range(samples):
        deg=random.randint(k,d)
        Wc=[random.randrange(q) for _ in range(deg)]+[random.randrange(1,q)]
        cands.append((Wc,f"rand{deg}"))
    ncw=0
    for Wc,desc in cands:
        if reduces_to_codeword(Wc): ncw+=1; continue
        Wv=[evalpoly(Wc,x) for x in mu]
        supply=0
        for cv in cw_vals:
            ac=sum(1 for i in range(n) if cv[i]==Wv[i])
            if ac>=a: supply+=comb(ac,a)
        if supply>best: best=supply; bestdesc=desc
    print(f"q={q},n={n},k={k},m={m}(a={a},d={d}): rand_mean={rand_mean:.4g}, "
          f"MAX non-codeword single-poly supply={best} [{bestdesc}], (codeword-skipped {ncw})")

run(17,8,2,1)    # n=8 > d=6, q=17
run(41,8,2,1)    # q=41 >> n=8
run(41,8,2,2)    # m=2: d=7 < n=8
run(73,8,2,1)    # q=73 >> n=8
run(11,10,2,1)   # n=10 > d=6, q=11
run(31,10,2,1)   # q=31 > n=10
run(41,10,2,2)   # n=10 > d=7
