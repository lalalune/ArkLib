#!/usr/bin/env python3
"""
C11 conductor-rank Katz GKM (analyst: secretly-open, = deep-moment E_r in AG form).

C11 claims: bound the period sup via a Katz GKM (Gauss-sum / hypergeometric sheaf) whose
conductor + generic rank + Swan conductor are <= K^r (p-independent), and Deligne Weil II
then gives sqrt-cancellation at the prize prime.

THE WALL (tested over proper mu_n, p>>n^3): Katz GKM controls the GENERIC RANK and the
HORIZONTAL/AVERAGE equidistribution (over the family / as q->infty), which is exactly the
r-th MOMENT count E_r(mu_n) -- the SAME deep-moment object as C04/C08/C12.  The conductor/rank
<= K^r bound IS the bound E_r <= (2r-1)!! n^r in AG language.  We verify the AG-moment identity:
   #{ (y_1..y_r, y'_1..y'_r) in mu_n^{2r} : sum y_i = sum y'_i } = E_r(mu_n)  (the period 2r-th moment)
and show it matches the Gaussian (Wick) count (2r-1)!! n^r to leading order -- i.e. the AG count
gives the AVERAGE moment (Johnson/Wick), NOT the single-prize-prime sup.  A flip-to-survives
needs the GKM to pin the sup at one prime, which Weil II (a q->inf / on-average statement) does not.
"""
import sympy
from math import gcd, sqrt, log
from itertools import product

def find_p_and_subgroup(n, mult=100):
    target=n**4; m=target//n
    while True:
        p=m*n+1
        if sympy.isprime(p) and p>mult*n**3 and (p-1)!=n:
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            mu=[pow(z,j,p) for j in range(n)]
            if len(set(mu))==n: return p,z,mu
        m+=1

def double_factorial(k):
    r=1
    while k>0: r*=k; k-=2
    return r

def Er_moment(mu, r, p):
    """E_r = #{(a in mu^r, b in mu^r): sum a = sum b mod p}.  = 2r-th additive energy moment."""
    from collections import Counter
    sums=Counter()
    for tup in product(mu, repeat=r):
        s=sum(tup)%p
        sums[s]+=1
    return sum(c*c for c in sums.values())

print("C11: AG-conductor count = additive 2r-th moment E_r of the subgroup periods.\n")
print(f"{'n':>4} {'r':>3} {'E_r (true)':>14} {'(2r-1)!! n^r (Wick/Johnson)':>28} {'ratio':>8}")
for mu in [3,4]:
    n=2**mu
    p,z,mu_set=find_p_and_subgroup(n)
    for r in [1,2,3]:
        if n**r > 200000:  # cap work
            break
        Er=Er_moment(mu_set, r, p)
        wick=double_factorial(2*r-1)*(n**r)
        print(f"{n:>4} {r:>3} {Er:>14} {wick:>28} {Er/wick:>8.4f}")
print("\nThe AG/GKM conductor-rank<=K^r bound IS E_r <= (2r-1)!! n^r (the Wick/Gaussian moment).")
print("This is the SAME deep-moment object as C04/C08/C12. It controls the AVERAGE (horizontal")
print("equidistribution / Weil-II on-average), giving the Johnson/Wick scale per rung.")
print("Pinning the single-prize-prime SUP M(mu_n) needs ALL rungs (deep-moment, forced anomaly")
print("E_r^{Fp} > E_r^{char0}) = the open BGK wall. Katz GKM gives generic rank, not the prime sup.")
print("VERDICT C11: secretly-open (deep-moment E_r in AG form).")
