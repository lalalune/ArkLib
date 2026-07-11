# Verify the weight-4 norm SIZE bound and derive the effective-Chebotarev COUNT bound.
# Proven: |Res(R, Phi_n)|^2 <= (4r)^phi(n) for weight <= 2r relations (cyclotomic resultant bound).
# For weight-4: 2r=4 => r=2 => |N|^2 <= 8^phi(n) => |N| <= 8^{phi(n)/2} = 8^{n/4} (n=2^m, phi=n/2).
# COUNT of distinct bad PRIZE primes (==1 mod n) dividing weight-4 norms:
#   each bad prime p >= n+1 (since p==1 mod n). p | some norm <= 8^{n/4}.
#   #distinct prime divisors of a fixed product of W norms, each <= 8^{n/4}, all > n:
#     <= log_n( prod ) = W * (n/4) * log_n(8) = W * (n/4)*3/log2(n).   (loose, but FINITE & explicit)
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product
import math
x=symbols('x')

for m in [4,5]:
    n=2**m;half=n//2;Phi=Poly(cyclotomic_poly(n,x),x)
    phi=n//2
    norms=set()
    bad_prize=set()
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
                    if pr%n==1: bad_prize.add(pr)
    maxnorm=max(norms)
    resbound = 8**(phi/2)   # (4r)^{phi/2}, r=2
    print(f"n={n} phi={phi}: max weight-4 |N|={maxnorm}, resbound 8^{{phi/2}}=8^{phi//2}={resbound} -> bound holds: {maxnorm<=resbound}")
    # effective-Chebotarev count bound on bad prize primes
    W=len(norms)
    # each bad prime > n, divides product of W norms each <= resbound
    count_bound = W * math.log(resbound)/math.log(n+1)
    print(f"  #distinct weight-4 norms W={W}; ACTUAL #bad prize primes={len(bad_prize)}; COUNT BOUND W*log(resbound)/log(n+1)={count_bound:.1f}")
    # tighter realistic: log2(prod of distinct norms)/log2(n+1)
    prod_log2 = sum(math.log2(N) for N in norms)
    print(f"  realistic count bound sum(log2 N)/log2(n+1) = {prod_log2/math.log2(n+1):.1f} (actual {len(bad_prize)})")
