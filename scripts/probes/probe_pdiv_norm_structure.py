# FASTER: normalize weight-4 antipodal-free relation by the unit zeta^a so the smallest
# exponent is 0: sigma = 1 +/- zeta^b +/- zeta^c +/- zeta^d, 0<b<c<d<n, antipodal-free.
# This collapses the unit orbit (factor n*2 in count). Compute N and factor.
# GOAL: understand which odd primes divide, and find the v2(p-1) stratification + a closed form.
import sympy as sp
from sympy import symbols, resultant, cyclotomic_poly, factorint, Poly
from itertools import combinations, product

x=symbols('x')
def v2(k):
    c=0
    while k and k%2==0: k//=2;c+=1
    return c

def probe(m):
    n=2**m; half=n//2
    Phi=Poly(cyclotomic_poly(n,x),x)
    norms={}   # |N| -> example
    for combo in combinations(range(1,n),3):  # b,c,d in 1..n-1
        exps=(0,)+combo
        if any(abs(a-b)==half for a,b in combinations(exps,2)): continue
        for signs in product([1,-1],repeat=3):
            sg=(1,)+signs
            R=Poly(sum(s*x**e for e,s in zip(exps,sg)),x)
            if R.is_zero: continue
            N=abs(int(resultant(R.as_expr(),Phi.as_expr(),x)))
            if N and N not in norms:
                norms[N]=(exps,sg)
    return norms,n

for m in [3,4,5]:
    norms,n=probe(m)
    odd=set()
    for N in norms:
        for pr in factorint(N):
            if pr!=2: odd.add(pr)
    odd=sorted(odd)
    print(f"=== n=2^{m}={n} ===  #distinct |N|={len(norms)}")
    print(f"  values: {sorted(norms)[:25]}")
    print(f"  odd prime divisors: {odd[:60]}")
    prize=[(p,v2(p-1)) for p in odd if p%n==1]
    print(f"  PRIZE (p==1 mod {n}) divisors w/ v2(p-1): {prize}")
    # also: are ALL odd divisors == +-1 mod something? check p mod n
    print(f"  odd divisors mod {n}: {sorted(set(p%n for p in odd))}")
