#!/usr/bin/env python3
"""
N1/S3 decisive test: does the SMOOTH structure of mu_n inflate value-
multiplicities (=> large window-interior list) vs a generic domain?

The window-interior list-size proxy: for a degree-D map f, #{values taken
>= a times by f on the domain} (each high-mult value = a codeword agreeing
with the folded word on >= a points). N1 conjectures a collision SAVING for
mu_n (O(D + n/log n)); the refutation is that mu_n forces super-poly high-
mult values (BKR-style). Computable at large n (O(n) per map).

Compare, at matched (n, D, window radius a):
  (S) smooth domain mu_n   vs   (G) generic random n-subset of F_p.
For each, sweep many degree-D polys (random + coset-structured) and report
the MAX #{values with multiplicity >= a} in the window a in (rho*n, sqrt(rho)*n).
If smooth >> generic and grows with n => N1 refuted, window list inflated by
structure (negative resolution signal). If comparable/bounded => saving
plausible.
"""
import math, random
from collections import Counter

def find_prime(n, lo):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for gg in range(2,p):
        h=pow(gg,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,j,p) for j in range(n)]
    raise RuntimeError
def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r

def max_highmult(dom, p, D, a_lo, a_hi, trials, rng, structured):
    best={a:0 for a in range(a_lo,a_hi+1)}
    n=len(dom)
    for _ in range(trials):
        if structured:
            # coset-structured: low-degree on each parity class (BKR-style)
            cA=[rng.randrange(p) for _ in range(D+1)]
            cB=[rng.randrange(p) for _ in range(D+1)]
            vals=[peval(cA if i%2==0 else cB, dom[i], p) for i in range(n)]
        else:
            c=[rng.randrange(p) for _ in range(D+1)]
            vals=[peval(c,dom[i],p) for i in range(n)]
        mult=Counter(vals)
        for a in range(a_lo,a_hi+1):
            hm=sum(1 for v,m in mult.items() if m>=a)
            if hm>best[a]: best[a]=hm
    return best

random.seed(13)
print("n   D  win[a_lo,a_hi] | SMOOTH max#highmult / GENERIC max#highmult (per a)")
for mu in (5,6,7,8,9,10):
    n=2**mu; p=find_prime(n, 50*n)
    D=2  # k=3 code -> deg<3 codewords; folded word agreement = value-mult of a deg-2-ish map proxy
    # window agreement (capacity .. Johnson) for rate rho=D/n? use rho s.t. window nonempty:
    rho=0.5  # constant-rate proxy: treat k=rho*n, but map degree fixed small D for the proxy
    a_lo=max(3, int(rho*n)//2); a_hi=math.ceil(math.sqrt(max(1,int(rho*n))*n))
    a_lo=min(a_lo,a_hi); 
    # sample a few representative a in window
    aS=sorted(set([a_lo, (a_lo+a_hi)//2, a_hi]))
    Dsm=smooth(p,n); Dgen=random.sample(range(1,p), n)
    bs=max_highmult(Dsm,p,D,min(aS),max(aS),30,random.Random(1),True)
    bg=max_highmult(Dgen,p,D,min(aS),max(aS),30,random.Random(2),True)
    sm={a:bs[a] for a in aS}; gn={a:bg[a] for a in aS}
    print(f"{n:4d} {D}  a in {aS} | smooth {sm}  generic {gn}")
