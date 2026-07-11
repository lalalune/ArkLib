#!/usr/bin/env python3
"""Validate the EXACT sibling-identified open quantity (AdditiveEnergyKernel): the BGK additive-energy
M = bgkCount n = #{u ∈ μ_n : -(1+u) ∈ μ_n} for a 2^k multiplicative subgroup μ_n ⊂ F_p, in the regime
|μ_n| = n ≪ √p. Bourgain-Glibichuk-Konyagin predict M ≪ n^{1/2+o(1)} (⟺ E(G)≪n^{5/2}). Confirm M is
sub-linear (beats trivial n) and tracks √n for 2-power subgroups."""
import math
def subgroup_2pow(p, k):
    # multiplicative subgroup of order n=2^k in F_p (needs 2^k | p-1)
    n = 2**k
    if (p-1) % n: return None
    g = None
    for cand in range(2, p):
        o=1; y=cand%p
        while y!=1: y=(y*cand)%p; o+=1
        if o==p-1: g=cand; break
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h,i,p) for i in range(n)})
def bgkM(p, mu):
    S=set(mu); cnt=0
    for u in mu:
        v=(-(1+u))%p
        if v in S: cnt+=1
    return cnt
print(f"{'p':>7} {'k':>2} {'n=2^k':>6} {'M':>4} {'sqrt(n)':>7} {'M/sqrt(n)':>9} {'n/sqrt(p)':>9} (want n<<sqrt(p))")
# pick primes p ≡ 1 mod 2^k with n ≪ √p
cases=[]
for k in range(2,8):
    n=2**k
    # find a prime p with 2^k | p-1 and p >> n^2 (so n ≪ √p)
    target=max(4*n*n, 200)
    p=target
    while True:
        p+=1
        if (p-1)%n: continue
        # primality
        if all(p%d for d in range(2,int(p**0.5)+1)):
            cases.append((p,k)); break
for (p,k) in cases:
    mu=subgroup_2pow(p,k)
    if mu is None or len(mu)!=2**k: continue
    n=2**k; M=bgkM(p,mu)
    print(f"{p:>7} {k:>2} {n:>6} {M:>4} {math.sqrt(n):>7.2f} {M/math.sqrt(n):>9.3f} {n/math.sqrt(p):>9.3f}")
