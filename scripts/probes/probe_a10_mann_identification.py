#!/usr/bin/env python3
"""
A10 final: IDENTIFY the residual algebraic deficit as the Mann/antipodal pairing structure.
mu_{2^mu} contains -1 (it's 2-power, so zeta^{n/2}=-1). Hence for any subset T containing a
pair {z,-z}, swapping does nothing but other antipodal swaps create EXACT (p-independent)
sum collisions: sum stays equal iff the multiset of +/- pairs matches. This is precisely the
vanishing-sum (Mann) structure. We confirm the t=n/2 deficit fraction is STABLE in n (= a
Mann constant) and check that REMOVING antipodal structure (a random Sidon set, no -1)
kills the deficit. If so: the A10 entropy gain IS the Mann count = reduces-to-Johnson.
PROPER REGIME p>>n^3.
"""
import itertools, math, sys, random
from math import comb, log2, lgamma, sqrt

def isprime(m):
    if m<2:return False
    if m%2==0:return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0:continue
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:ok=True;break
        if not ok:return False
    return True
def find_prime(n,e):
    lo=int(n**e);t=((lo//n)+1)*n+1
    while not isprime(t):t+=n
    return t
def subgroup(p,n):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fac.append(x)
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac):g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return H
def log2binom(n,k):
    if k<0 or k>n:return float("-inf")
    if k in(0,n):return 0.0
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/math.log(2)
def ndist(D,t,p):
    return len({sum(c)%p for c in itertools.combinations(D,t)})

def main():
    print("A10 Mann-identification: is the residual deficit the antipodal/Mann vanishing-sum count?")
    print("mu_n (has -1) vs random Sidon set (no antipodal pairs). t=n/2.")
    print()
    print(f"{'n':>3} {'t':>3} | {'mu_n N/C':>9} {'mu_n def/l2C':>12} | {'Sidon N/C':>10} {'Sidon def/l2C':>13}")
    print("-"*70)
    random.seed(3)
    for mu in (3,4,5):
        n=1<<mu; t=n//2
        if comb(n,t)>50_000_000: continue
        p=find_prime(n,4.5)
        D=subgroup(p,n)
        R=sorted(random.sample(range(1,p),n))
        l2c=log2binom(n,t)
        Nm=ndist(D,t,p); Nr=ndist(R,t,p)
        defm=l2c-log2(Nm); defr=l2c-log2(Nr)
        print(f"{n:>3} {t:>3} | {Nm/comb(n,t):>9.4f} {defm/l2c:>12.4f} | {Nr/comb(n,t):>10.4f} {defr/l2c:>13.4f}")
    print()
    print("INTERPRETATION: if mu_n deficit >> Sidon deficit AND mu_n def/l2C ~ stable const,")
    print("the gain is the antipodal/Mann structure (z,-z pairs) = the PROVEN-DEAD Mann count.")
    print("Sidon ~ 0 deficit confirms generic sets have NO algebraic collisions (=volume).")
    return 0
if __name__=="__main__":
    sys.exit(main())
