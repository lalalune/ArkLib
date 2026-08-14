#!/usr/bin/env python3
"""
A10 -- THE LOAD-BEARING TEST: is the worst-case BAD LIST actually bounded by the
subset-sum entropy envelope Lambda_r = 2^H, OR is the entropy a red herring that
does NOT bound the list?

Probe 2 showed the subset-sum law has an ALGEBRAIC (p-stable) concentration: #distinct
(r+1)-subset sums plateaus at a CEILING < C(n, r+1) as p grows. The A10 NEW LEMMA
asserts: worst-case far-line list L <= Lambda_r. THIS PROBE TESTS THE INEQUALITY DIRECTLY.

The actual prize object (in-tree, validated by probe_jump_subsetsum.py): at the jump
radius delta = 1-(k+1)/n for the monomial stack u0=x^{k+1}, u1=x^k, the bad count over
gamma in F_p equals the number of DISTINCT (k+1)-subset sums of the domain (proven
empirically there). The far-line LIST (codewords) at the jump is THIS bad count.

So the in-tree fact is:  L_jump = #distinct (k+1)-subset sums =: N_dist.
And Lambda_r = 2^{H(P_r)} <= N_dist always (entropy <= log support). So:
   Lambda_r <= N_dist = L_jump.
i.e. the entropy envelope is a LOWER bound on the list, not an upper bound!
That would REFUTE the A10 direction (entropy does not cap the list; it's below it).

TEST: compute, exactly, at the jump radius:
   (a) L_jump = worst-case bad list (=#distinct (k+1)-subset sums, re-verify),
   (b) Lambda_r = 2^H, N_dist = #distinct,
   (c) the budget B = eps*q in window, the volume C(n,k+1), Johnson list bound.
Determine: does Lambda_r UPPER-bound L (A10 lemma true) or LOWER-bound it (A10 false)?
And separately: is N_dist (the actual list) itself below budget past Johnson? (That would
be a win regardless of entropy -- the "distinct subset sum count" bound.)

PROPER REGIME p PRIME, n=2^mu, n|p-1, p>>n^3.
"""
import itertools, math, sys
from collections import Counter
from math import comb, log2, lgamma, sqrt

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True

def find_prime(n, e):
    lo=int(n**e); t=((lo//n)+1)*n+1
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
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return H

def log2binom(n,k):
    if k<0 or k>n: return float("-inf")
    if k in (0,n): return 0.0
    return (lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1))/math.log(2)

def subset_sum_stats(D,t,p):
    cnt=Counter()
    for cmb in itertools.combinations(D,t): cnt[sum(cmb)%p]+=1
    total=comb(len(D),t)
    H=-sum((c/total)*log2(c/total) for c in cnt.values() if c)
    return H, len(cnt), 2**H, total

def main():
    print("A10 LOAD-BEARING: does Lambda_r=2^H UPPER-bound the list (A10 true) or LOWER-bound it?")
    print("In-tree fact: L_jump = #distinct (k+1)-subset sums = N_dist. Entropy <= log N_dist always,")
    print("so Lambda_r <= N_dist = L_jump. If so A10's 'list <= entropy' is BACKWARDS (refuted).")
    print()
    print(f"{'n':>3} {'k':>2} {'t=k+1':>5} {'p':>10} | {'N_dist=L_jump':>13} {'Lambda=2^H':>11} "
          f"{'C(n,t)':>9} {'delta':>6} {'Johnson':>8} {'cap':>6}")
    print("-"*110)
    for (mu,k) in [(3,1),(3,2),(4,2),(4,3),(4,5),(5,3),(5,5),(5,7)]:
        n=1<<mu; t=k+1
        if t>n: continue
        rho=k/n  # rate ~ k/n (deg<k code, length n)
        p=find_prime(n,4.0)
        D=subgroup(p,n)
        H,Ndist,Lam,total=subset_sum_stats(D,t,p)
        delta=1-t/n
        johnson=1-sqrt(rho); cap=1-rho
        l2c=log2binom(n,t)
        print(f"{n:>3} {k:>2} {t:>5} {p:>10} | {Ndist:>13} {Lam:>11.1f} "
              f"{total:>9} {delta:>6.3f} {johnson:>8.3f} {cap:>6.3f}")
    print()
    print("KEY: 'past Johnson' window = delta in (johnson, cap). At the jump radius delta=1-(k+1)/n")
    print("with k+1 small, delta is NEAR 1 (deep past Johnson) but that's the FLOOR end. Compare")
    print("N_dist (the true list) to budget eps*q in window. Lambda <= N_dist means A10 is backwards.")
    return 0

if __name__=="__main__":
    sys.exit(main())
