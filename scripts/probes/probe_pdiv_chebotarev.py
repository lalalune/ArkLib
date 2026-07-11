# CLAIM: a prime p with a primitive 2^m-th root in F_p (m>=2) must be == 1 mod 4.
# (Because i = g^{2^{m-2}} has i^2 = g^{2^{m-1}} = -1, so -1 is a QR mod p.)
# Consequence: any p that is == 3 mod 4 has NO primitive 2^m-th root for m>=2, so mu_{2^m}
# does not embed in F_p at all -> Spur contribution = 0 from that field directly.
# BUT spurious collisions can happen in EXTENSION fields F_{p^f}. The norm-level statement:
#   p | N(sigma_T) iff sigma_T == 0 in F_{p^f}, f = ord_{2^m}(p).
# For p == 3 mod 4: does p divide any weight-4 (or general) antipodal-free norm to ODD power?
# The s2s law says NO (odd power of a 3-mod-4 prime can't divide a sum of two squares).
# Verify: for p==3 mod 4 dividing a weight-4 norm, the p-adic valuation is always EVEN.
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product
x=symbols('x')

for m in [4,5]:
    n=2**m;half=n//2;Phi=Poly(cyclotomic_poly(n,x),x)
    viol=0;checked=0;p3_odd_power=0
    for combo in combinations(range(1,n),3):
        exps=(0,)+combo
        if any(abs(a-b)==half for a,b in combinations(exps,2)):continue
        for signs in product([1,-1],repeat=3):
            sg=(1,)+signs
            R=Poly(sum(s*x**e for e,s in zip(exps,sg)),x)
            if R.is_zero:continue
            N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
            checked+=1
            for pr,e in factorint(N).items():
                if pr%4==3 and e%2==1:
                    p3_odd_power+=1
                    print(f"  VIOLATION m={m}: prime {pr}==3mod4 to ODD power {e} in N={N}")
    print(f"m={m}: checked {checked} weight-4 norms; primes==3mod4 to odd power: {p3_odd_power}")

# Direct embedding check: smallest p==3 mod 4 with 2^m-th root? (should be NONE for m>=2)
print("\nDirect: does any p==3 mod 4 admit a primitive 2^m-th root (m>=2)?")
for m in [2,3,4,5]:
    n=2**m
    found=[p for p in sp.primerange(3,5000) if p%4==3 and (p-1)%n==0]
    print(f"  m={m} n={n}: primes p==3mod4 with n|(p-1): {found[:5]} (should be empty)")
