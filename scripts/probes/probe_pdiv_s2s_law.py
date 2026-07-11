# CONFIRM the law across m=3,4,5 and find the MECHANISM.
# Hypothesis: N(sigma_T) for weight-4 antipodal-free is a sum of two squares (odd part),
#   equivalently primes == 3 mod 4 divide only to even power. WHY:
#   Z[zeta_{2^m}] (m>=2) contains i = zeta_{2^m}^{2^{m-2}} (a primitive 4th root). The norm
#   N_{Q(zeta)/Q}(x) = N_{Q(i)/Q}(N_{Q(zeta)/Q(i)}(x)) = |alpha|^2-form -> sum of two squares.
#   Actually N_{Q(zeta)/Q} factors through Q(i): N(x) = Norm_{Q(i)/Q}(Norm_{Q(zeta)/Q(i)}(x)),
#   and Norm_{Q(i)/Q}(a+bi)=a^2+b^2. So EVERY norm from Q(zeta_{2^m}), m>=2, is a sum of two squares!
#   That's the mechanism and it's WEIGHT-INDEPENDENT. Test on weight-4 AND general.
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product
x=symbols('x')
def is_s2s(N):
    if N==0:return True
    for pr,e in factorint(N).items():
        if pr%4==3 and e%2==1:return False
    return True

for m in [3,4,5]:
    n=2**m;half=n//2;Phi=Poly(cyclotomic_poly(n,x),x)
    allgood=True;cnt=0
    for combo in combinations(range(1,n),3):
        exps=(0,)+combo
        if any(abs(a-b)==half for a,b in combinations(exps,2)):continue
        for signs in product([1,-1],repeat=3):
            sg=(1,)+signs
            R=Poly(sum(s*x**e for e,s in zip(exps,sg)),x)
            if R.is_zero:continue
            N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
            cnt+=1
            if not is_s2s(N):allgood=False;print(f"  COUNTEREXAMPLE m={m}: N={N} exps={exps} signs={sg}")
    print(f"m={m} n={n}: ALL {cnt} weight-4 norms are sum-of-two-squares: {allgood}")

# Now test the GENERAL claim: ANY norm from Q(zeta_{2^m}) m>=2 is s2s (weight-independent).
# Test random weight-6 and weight-8.
import random
print("\nGeneral (weight 6,8 random) s2s test m=5:")
m=5;n=2**m;Phi=Poly(cyclotomic_poly(n,x),x)
bad=0
for trial in range(300):
    w=random.choice([6,8,5,7])
    exps=random.sample(range(n),w)
    sgs=[random.choice([1,-1]) for _ in range(w)]
    R=Poly(sum(s*x**e for e,s in zip(exps,sgs)),x)
    if R.is_zero:continue
    N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
    if not is_s2s(N):bad+=1;print(f"  NON-s2s: w={w} N={N}")
print(f"  non-s2s count among 300 random arbitrary-weight: {bad}")
