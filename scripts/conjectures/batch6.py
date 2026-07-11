#!/usr/bin/env python3
"""Batch 6: fold/doubling recursion for moments (from the Bessel GF), intersection-distribution
completeness, signed/restricted moments. Cheap (n<=32)."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import big_prime_pow, mu, energyR, test_conjecture, SURVIVORS, DEAD
from collections import Counter
from fractions import Fraction
import math, itertools

def Gp(n,power): p=big_prime_pow(n,power); return mu(p,n),p
def Er(m,r):
    n=1<<m; G,p=Gp(n,r+1); return energyR(G,p,r)

# F1 (NOVEL, from Bessel GF): E_r(mu_{2n}) = (2r)! * sum_{a+b=r} (E_a/(2a)!)(E_b/(2b)!) at mu_n
#   since [x^r] f^n = sum_{a+b=r} [x^a]f^{n/2} [x^b]f^{n/2}.  (E_0 := 1.)
def fold_pred(m, r):
    # predict E_r(mu_{2^{m+1}}) from E_*(mu_{2^m})
    Es = {a: (1 if a==0 else Er(m,a)) for a in range(r+1)}
    s = sum(Fraction(Es[a], math.factorial(2*a)) * Fraction(Es[r-a], math.factorial(2*(r-a)))
            for a in range(r+1))
    return math.factorial(2*r) * s
for r in [2,3,4]:
    test_conjecture(f"F{r}",f"E_{r}(μ_2n) = (2r)!·Σ_(a+b=r) E_a(μ_n)/(2a)!·E_b(μ_n)/(2b)! (fold/Bessel recursion)",
        lambda m,rr=r:Er(m+1,rr), lambda m,rr=r:fold_pred(m,rr), [2,3,4],"NOVEL-recursion")

# F4 (NOVEL): intersection-distribution completeness — N(0)=n, and only values {0,1,2} occur
def maxN(m):
    n=1<<m; G,p=Gp(n,3)
    d=Counter()
    for a in G:
        for b in G:
            if a!=b: d[(a-b)%p]+=1
    return max(d.values()) if d else 0
test_conjecture("Cmax","max_{t≠0} |μ_n ∩ (μ_n−t)| = 2 (Sidon-mod-neg, the structural heart)",
    lambda m:2, maxN, [2,3,4,5],"NOVEL-structural")

# F5 (NOVEL): N(0) = #{(a,b): a-b=0... } no; the count of c with c+0... trivial. Instead:
# the 'self-difference' Σ_t N(t)^2 over t!=0 equals E_2 - n^2 (consistency); restate as identity
def diffE_minus(m):
    n=1<<m; G,p=Gp(n,2)
    d=Counter()
    for a in G:
        for b in G:
            if a!=b: d[(a-b)%p]+=1
    return sum(v*v for v in d.values())
test_conjecture("Cd2","Σ_{t≠0} |μ_n∩(μ_n−t)|² = 2n²−5n+2 ... test",  # guess; will refute/fit
    lambda m:(lambda n:2*n*n-5*n+2)(1<<m), diffE_minus, [2,3,4,5],"NOVEL(guess)")

# F6 (NOVEL): signed moment — #{(a,b,c,d): a+b = c+d, all distinct} (genuine-Sidon restricted)
def E2_distinct(m):
    n=1<<m; G,p=Gp(n,2); S=list(G)
    cnt=0
    sums=Counter()
    for i in range(n):
        for j in range(n):
            if i!=j: sums[(S[i]+S[j])%p]+=1   # a!=b
    return sum(v*v for v in sums.values())
test_conjecture("Csd","E_2 restricted to a≠b: Σ r'(c)² = n²−n ... test",
    lambda m:(lambda n:n*n-n)(1<<m), E2_distinct, [2,3,4,5],"NOVEL(guess)")

# F7 (NOVEL): #{(a,b)∈μ_n²: a²+b²∈μ_n} (a quadratic-additive count)
def sq_sum(m):
    n=1<<m; G,p=Gp(n,3); S=set(G)
    return sum(1 for a in G for b in G if (a*a+b*b)%p in S)
def cnt_sqsum(m):
    return sq_sum(m)
pts=[2,3,4,5]; ns=[1<<m for m in pts]; ys=[cnt_sqsum(m) for m in pts]
print("a²+b²∈μ_n count:", list(zip(ns,ys)))

print("\n==== BATCH 6 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")
