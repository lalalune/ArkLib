#!/usr/bin/env python3
"""
PROBE (CORRECTED): the Q1ArisingFamilyDescent agreement/orbit descent operates on PENCIL
exponents (a,b) via d = gcd(a,b,n). It reduces deployment pencil z^a+alpha z^b on mu_n to a
base pencil on mu_{n/d}. The reduction factor is d = gcd(a,b,n).

TWO clean facts to confirm before formalizing the EXTEND brick + constraint lemma:
(1) DESCENT VACUITY: when d = gcd(a,b,n) = 1 (PRIMITIVE pencil), orbitSize_descent is the
    IDENTITY (n/1, a/1, b/1) -- the descent gives NO reduction. (a Nat fact, exact)
(2) PRIMITIVE-DIRECTION DENSITY: among the (b-a) mod n exponent-difference directions, the
    fraction with gcd(b-a, n) = 1 (where the orbit group is the FULL mu_n, orbitSize = 1,
    most bad orbits, the HARD case) -> for n = 2^a, gcd(odd, 2^a)=1, so exactly the ODD
    differences are primitive = HALF of all directions. The descent reduces NONE of these.

So the descent covers only the EVEN-difference (imprimitive) pencils; the ODD-difference
(primitive) half -- which includes the worst orbit structure (orbitSize=1, full mu_n acting)
-- is UNTOUCHED. The fold-transport lever provably cannot reduce the primitive-direction
worst case.
"""
import math

print("=== (1) descent vacuity at d=1: orbitSize(n,a,b) == orbitSize(n/1,a/1,b/1) ===")
def orbitSize(n,a,b): return n // math.gcd(b-a, n) if b>=a else n // math.gcd(a-b,n)
ok=True
for n in [4,8,16,32,64,128,256]:
    for a in range(0,n):
        for b in range(a,n):
            if math.gcd(math.gcd(a,b),n)==1:  # primitive pencil d=1
                if orbitSize(n,a,b)!=orbitSize(n//1,a//1,b//1):
                    ok=False
print(f"  d=1 descent is identity: {ok} (trivially -- /1)")

print()
print("=== (2) primitive-direction (odd diff, gcd(b-a,n)=1) density for n=2^a ===")
print("n     #odd-diff(primitive)  #even-diff  primitive-fraction  these have orbitSize=1?")
for a in range(2,9):
    n=2**a
    odd=0; even=0; allOrbit1=True
    for d in range(1,n):  # exponent difference b-a mod n, d in 1..n-1
        if math.gcd(d,n)==1:
            odd+=1
            if n//math.gcd(d,n)!=n: allOrbit1=False
        else:
            even+=1
    print(f"{n:<5} {odd:<20} {even:<11} {odd/(n-1):.3f}              orbitSize==n: {allOrbit1}")

print()
print("=== KEY: for n=2^a, gcd(d,n)=1 <=> d ODD. The descent reduces a deployment pencil")
print("    ONLY when gcd(a,b,n)>1. The primitive directions (orbit group = full mu_n,")
print("    orbitSize = n, the MOST bad orbits) are EXACTLY the odd-difference ones; the")
print("    descent is the IDENTITY there. The fold-transport lever leaves the hard half untouched.")
