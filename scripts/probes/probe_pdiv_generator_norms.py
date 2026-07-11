# wf-C1 effective-Chebotarev: a prime p is "weight-4 bad" iff p | N(σ_T) for SOME antipodal-free
# weight-4 T. The set of distinct norm VALUES N(σ_T) is FINITE (depends only on n=2^m, not p).
# So the bad-prime set = {p : p | LCM/product of these finitely many norms} = primes dividing a
# FIXED integer D_4(n) = product of distinct odd parts of weight-4 norms. The effective-Chebotarev
# COUNT of bad primes up to X is then #{p<=X : p | D_4(n)} = omega-type, bounded by log D_4(n)/log 2.
# CONFIRM: the bad prize primes are EXACTLY the prime divisors of the weight-4 norm value set.
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product
x=symbols('x')

def weight4_norm_primes(m):
    n=2**m;half=n//2;Phi=Poly(cyclotomic_poly(n,x),x)
    odd_primes=set()
    norms=set()
    for combo in combinations(range(1,n),3):
        exps=(0,)+combo
        if any(abs(a-b)==half for a,b in combinations(exps,2)):continue
        for signs in product([1,-1],repeat=3):
            sg=(1,)+signs
            R=Poly(sum(s*x**e for e,s in zip(exps,sg)),x)
            if R.is_zero:continue
            N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
            if N:
                norms.add(N)
                for pr in factorint(N):
                    if pr!=2:odd_primes.add(pr)
    return odd_primes, norms

for m in [4,5]:
    n=2**m
    odd_primes, norms = weight4_norm_primes(m)
    # the bad PRIZE primes (p==1 mod n) are exactly those odd norm-divisors that are ==1 mod n
    bad_prize = sorted(p for p in odd_primes if p%n==1)
    print(f"n={n}: total distinct odd norm-prime-divisors={len(odd_primes)}")
    print(f"  bad PRIZE primes (==1 mod {n}) = norm divisors: {bad_prize[:25]}")
    # effective-Chebotarev count: #bad prize primes <= X is just the count of such divisors <= X
    # bound: each is a prime factor of some norm <= max norm. The COUNT is finite & small.
    maxnorm=max(norms)
    print(f"  max weight-4 norm = {maxnorm} (= 2^{sp.log(maxnorm,2).evalf():.1f} approx); #bad prize primes total (in computable range) = {len(bad_prize)}")
    # KEY: is bad-prize-prime-count bounded by log2(product of distinct norms)?  
    # The genuine effective-Chebotarev statement: density of bad primes among ALL primes -> 0 (finite set!)
    # NO — that's wrong: as m grows, norms grow, more primes. Let me check: is the bad set FINITE for fixed n?
    print(f"  => for FIXED n, the weight-4 bad-prize set is FINITE (subset of divisors of {len(norms)} fixed norms).")
