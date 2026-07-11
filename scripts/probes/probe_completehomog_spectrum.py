#!/usr/bin/env python3
"""probe_completehomog_spectrum.py (#444) — the F1 char-free floor open input.
#{distinct h_r(R): R in binom(mu_s,k+1)} (complete-homogeneous spectrum) vs poly*C(s+r-1,r).
FINDING: poly=1 FALSE (#distinct h_2(mu_16)=1848 > C(17,2)=136); poly=n SUFFICES (min poly <=14<=n
for s=8,16, all r<=6). So the ABF26 floor #bad <= poly(n)*C(s+r-1,r) holds with poly(n)=n (a
sub-leading log correction); leading delta* pinned by C(s+r-1,r). This spectrum bound (with poly=n)
is the single genuine open prize core (the char-free complete-homogeneous distinct-value count)."""
import itertools
from math import comb
def isprime(x):
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return x>1
def gen_prime(s,lo):
    p=max(lo,s+1)
    while not(p%s==1 and isprime(p)): p+=1
    return p
def subgroup(s,p):
    for g in range(2,p):
        h=pow(g,(p-1)//s,p)
        if pow(h,s,p)==1 and all(pow(h,s//q,p)!=1 for q in [2] if s%q==0):
            return [pow(h,i,p) for i in range(s)]
def hsym(R,r,p):
    dp=[0]*(r+1); dp[0]=1
    for x in R:
        ndp=dp[:]
        for j in range(1,r+1): ndp[j]=(dp[j]+x*ndp[j-1])%p
        dp=ndp
    return dp[r]
if __name__=="__main__":
    for s in [8,16]:
        p=gen_prime(s,50*s**4); S=subgroup(s,p); k=s//4
        print(f"s={s} k+1={k+1}:")
        for r in [2,3,4,5,6]:
            vals={hsym(R,r,p) for R in itertools.combinations(S,k+1)}
            ch=comb(s+r-1,r); polymin=(len(vals)+ch-1)//ch
            print(f"  r={r}: #distinct={len(vals)} C(s+r-1,r)={ch} poly_min={polymin} (<=n={s}: {polymin<=s})")
