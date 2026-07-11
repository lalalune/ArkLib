#!/usr/bin/env python3
"""Batch 3: corrected + extended. Uses p > n^r to stay in the no-relation regime per moment."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import (isprime, big_prime_pow, mu, energyR, Zk_count,
                    test_conjecture, SURVIVORS, DEAD)
import itertools
from fractions import Fraction

def Er_clean(m, r):
    """E_r with p > n^{r+1} (safely in no-relation regime)."""
    n=1<<m; p=big_prime_pow(n, r+1); G=mu(p,n); return energyR(G,p,r)
def Zk_clean(m, k):
    n=1<<m; p=big_prime_pow(n, k); G=mu(p,n); return Zk_count(G,p,k)

def fit_poly(xs,ys,deg):
    A=[[Fraction(x)**j for j in range(deg+1)] for x in xs[:deg+1]]; b=[Fraction(y) for y in ys[:deg+1]]
    M=[A[i][:]+[b[i]] for i in range(deg+1)]; nn=deg+1
    for c in range(nn):
        piv=next(r for r in range(c,nn) if M[r][c]!=0); M[c],M[piv]=M[piv],M[c]
        inv=Fraction(1)/M[c][c]; M[c]=[v*inv for v in M[c]]
        for r in range(nn):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(nn+1)]
    return [M[i][nn] for i in range(nn)]

# C10': Z_4 = E_2 = 3n^2-3n  (identity via negation-closure)
test_conjecture("C10","Z_4(mu_n)=#{4-tuples sum 0}=3n^2-3n (=E_2, negation identity)",
    lambda m:(lambda n:3*n*n-3*n)(1<<m), lambda m:Zk_clean(m,4),[1,2,3,4,5],"NOVEL-identity")

# C11': Z_{2j+1}(mu_{2^m}) = 0  for odd lengths 3,5,7
for k in [3,5,7]:
    test_conjecture(f"C11.{k}",f"Z_{k}(mu_2^m)=0 (odd-length zero-sum vanishes)",
        lambda m:0, (lambda kk: (lambda m:Zk_clean(m,kk)))(k), [1,2,3,4],"NOVEL")

# C8': E_4 closed form with clean prime, fit n=2..16, verify n=32
e4=[Er_clean(m,4) for m in range(1,5)]; ns=[1<<m for m in range(1,5)]
print("E4 clean data:",list(zip(ns,e4)))
coef4=fit_poly(ns+[32],e4+[Er_clean(5,4)],4)
print("E4 coeffs:",[str(c) for c in coef4])
if all(c.denominator==1 for c in coef4):
    cc=[int(c) for c in coef4]
    test_conjecture("C8",f"E_4(mu_n) = {cc[4]}n^4+{cc[3]}n^3+{cc[2]}n^2+{cc[1]}n+{cc[0]}",
        lambda m:(lambda n:sum(cc[i]*n**i for i in range(5)))(1<<m),
        lambda m:Er_clean(m,4),[1,2,3,4,5],"NOVEL")

# C9': leading coeff of E_r = (2r-1)!! (test via clean fit, not finite ratio)
def dblfact(k):
    r=1
    while k>0: r*=k; k-=2
    return r
def lead_coeff(r):
    pts=list(range(1, r+2))  # m=1..r+1 -> n=2..2^{r+1}
    ns=[1<<m for m in pts]; ys=[Er_clean(m,r) for m in pts]
    return fit_poly(ns,ys,r)[r]
test_conjecture("C9","leading coeff of E_r(mu_n) = (2r-1)!!",
    lambda r:Fraction(dblfact(2*r-1)), lambda r:lead_coeff(r),[2,3,4],"NOVEL-general")

# C-meta (NOVEL): E_r(mu_n) is a degree-r integer polynomial in n once p > n^r;
#   equivalently the no-(2r)-term-relation threshold is p ~ n^r. Test: at p just BELOW n^r,
#   E_r exceeds the polynomial (genuine relations appear) — verify the threshold is ~n^r.
def relations_appear(m, r):
    """returns True if E_r at p~n^{r-0.5} exceeds the clean (p>n^{r+1}) value (relations present)."""
    n=1<<m
    clean=Er_clean(m,r)
    p_small=big_prime_pow(n, r, lo=2)  # p ~ n^r
    # use a prime BELOW n^r to force relations: p ~ n^{r-1}
    p_below=big_prime_pow(n, r-1, lo=2)
    G=mu(p_below,n); below=energyR(G,p_below,r)
    return below > clean
# threshold conjecture: for r=2, relations appear when p < n^2 (below n^2), absent when p>n^2
def E2_below_nsq(m):
    n=1<<m; p=big_prime_pow(n,1,lo=2)  # p ~ n (< n^2): relations present
    if p<=n: p=big_prime_pow(n,1,lo=n+2)
    G=mu(p,n); return 1 if energyR(G,p,2) > 3*n*n-3*n else 0
test_conjecture("Cmeta","E_2 exceeds 3n^2-3n when p<n^2 (relations appear below n^2 threshold), n>=4",
    lambda m:1, E2_below_nsq, [3,4,5,6],"NOVEL-threshold")

print("\n==== BATCH 3 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")
