#!/usr/bin/env python3
"""
A10 follow-up: the ENTROPY lemma is refuted (Lambda=2^H <= N_dist = list, backwards).
But the SAME probe-trail exposes the real object: the worst-case list at the jump =
N_dist = #distinct (k+1)-subset sums of mu_n. Is N_dist itself below budget past Johnson,
and HOW does N_dist/C(n,k+1) scale (=the algebraic concentration deficit)?

If N_dist << C and below budget in the window => a real bound, BUT it is a SUBSET-SUM
COUNT bound = exactly the Mann/vanishing-sum count, which the manifesto lists as PROVEN
DEAD (antipodal/Mann = Johnson boundary). So this would REDUCE-TO-JOHNSON, not crack.

We quantify: (1) N_dist/C(n,t) vs n,t (deficit). (2) does N_dist beat the budget eps*q at
prize scale (eps=2^-128, q~n^4)? If N_dist > q*eps in the window for all n -> no win.
(3) Crucially: is the deficit log2(C/N_dist) growing like the gain so it tracks Johnson's
1-sqrt(rho) or the floor's 1-rho-1/log? Compare 1-(k+1)/n to those.

We compute N_dist EXACTLY where feasible (sum mod a LARGE prime p>>n^3, so N_dist =
algebraic distinct count since collisions plateaued in probe 2).
PROPER REGIME p PRIME n=2^mu n|p-1 p>>n^3.
"""
import itertools, math, sys
from collections import Counter
from math import comb, log2, lgamma, sqrt

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:ok=True;break
        if not ok: return False
    return True

def find_prime(n,e):
    lo=int(n**e);t=((lo//n)+1)*n+1
    while not isprime(t): t+=n
    return t

def subgroup(p,n):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1: fac.append(x)
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac):g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return H

def log2binom(n,k):
    if k<0 or k>n: return float("-inf")
    if k in (0,n): return 0.0
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/math.log(2)

def ndistinct(D,t,p):
    s=set()
    for cmb in itertools.combinations(D,t): s.add(sum(cmb)%p)
    return len(s)

def main():
    print("A10 follow-up: N_dist=#distinct (k+1)-subset sums = the WORST-CASE LIST at the jump.")
    print("deficit = log2(C/N_dist). Budget at prize scale: B = eps*q, eps=2^-128, q=n^4 => log2 B = 4 log2 n -128 (NEGATIVE for all feasible n -> budget < 1!).")
    print("So 'list <= budget' needs list O(1). Track log2 N_dist vs log2 C vs deficit.")
    print()
    print(f"{'n':>4} {'t':>3} {'log2C':>7} {'log2 Ndist':>10} {'deficit':>8} {'def/log2C':>9} {'N/C':>7} {'delta':>6} {'1-sqrt(t/n)':>11}")
    print("-"*95)
    rows=[]
    for mu in (3,4,5,6):
        n=1<<mu
        p=find_prime(n,4.0)
        D=subgroup(p,n)
        # t small (jump end) and t~n/2 (where surplus lives)
        for t in sorted(set([2,3,4, n//4 if n//4>=2 else 2, n//2])):
            if t<2 or t>n-1: continue
            if comb(n,t) > 60_000_000:  # enumeration cap
                continue
            Nd=ndistinct(D,t,p)
            l2c=log2binom(n,t); l2N=log2(Nd) if Nd else 0
            deficit=l2c-l2N
            delta=1-t/n; rho=t/n
            print(f"{n:>4} {t:>3} {l2c:>7.3f} {l2N:>10.3f} {deficit:>8.3f} {deficit/l2c:>9.4f} {Nd/comb(n,t):>7.4f} {delta:>6.3f} {1-sqrt(rho):>11.3f}")
            rows.append((n,t,l2c,l2N,deficit))
        print()
    print("VERDICT: budget at prize scale eps*q with eps=2^-128 is TINY (often <1), so ANY list")
    print(">=1 may exceed it -- the budget question is about the FRACTION of bad gammas, not raw count.")
    print("If deficit/log2C -> a CONSTANT c<1 (not ->1), then N_dist = C^{1-c} = a POWER of the volume:")
    print("an exponent IMPROVEMENT over volume but still EXPONENTIAL => does NOT reach O(budget); and")
    print("it is a pure subset-sum-count = Mann count => reduces-to-Johnson. If deficit/log2C -> 0, no gain.")
    return 0

if __name__=="__main__":
    sys.exit(main())
