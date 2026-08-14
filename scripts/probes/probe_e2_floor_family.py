#!/usr/bin/env python3
"""
PROBE 5: identify the EXACT guaranteed additive-quadruple families giving the 3n^2-3n floor
for a NEGATION-CLOSED set S (-S = S), no extra coincidences (near-Sidon case n small).
We want to express E2 floor = 3n^2 - 3n as a union of explicitly-parametrized solution
families of a+b = c+d that exist for ANY negation-closed n-set with otherwise-Sidon sums.

Families of (a,b,c,d) in S^4 with a+b=c+d that hold for ANY set:
  F1: (a,b,a,b)            n^2
  F2: (a,b,b,a)            n^2     (overlap F1 on a=b: n)
For a NEGATION-CLOSED set (-S=S), extra guaranteed family from a+b = c+d with the
substitution using s in S, -s in S:
  F3: (a, -a, b, -b)  for all a,b  =>  a+(-a)=0=b+(-b).  n^2 solutions, sum 0 on both sides.
      overlaps F1/F2 when {a,-a}={... }.
Count the DISJOINT union carefully via direct enumeration on a small near-Sidon symmetric set
and match to 3n^2-3n. Then state the floor decomposition.
"""
import sympy
from collections import Counter

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def classify(p, n):
    S = subgroup(p,n)
    Sset = set(S)
    neg_closed = all((p-x)%p in Sset for x in S)
    # enumerate all additive quadruples a+b=c+d mod p
    total = 0
    f1 = f2 = f3 = 0
    sols = []
    for a in S:
        for b in S:
            for c in S:
                for d in S:
                    if (a+b)%p == (c+d)%p:
                        total += 1
                        if (a,b)==(c,d): f1+=1
                        elif (a,b)==(d,c): f2+=1
                        elif (b%p)==(p-a)%p and (d%p)==(p-c)%p: f3+=1
    floor = 3*n*n-3*n
    return neg_closed, total, floor

print(f"{'p':>6} {'n':>4} {'negclosed':>9} {'E2':>8} {'3n^2-3n':>8} {'eq?':>5}")
for p,nlist in [(769,[4,8,16,32]),(7681,[8,16,32]),(40961,[16,32])]:
    for n in nlist:
        if (p-1)%n: continue
        nc, tot, fl = classify(p,n)
        print(f"{p:>6} {n:>4} {str(nc):>9} {tot:>8} {fl:>8} {str(tot==fl):>5}")
print()
print("Floor 3n^2-3n decomposition (negation-closed near-Sidon set):")
print(" F1 (a,b,a,b): n^2 ; F2 (a,b,b,a): n^2 ; F3 (a,-a,c,-c): n^2 ;")
print(" minus overlaps. 3n^2 - (overlaps=3n) = 3n^2-3n. Overlaps: F1∩F2 (a=b): n;")
print(" F1∩F3 (b=-a & b=a => a=-a, only if 2a=0, none for odd p, BUT a=b & -a=b => a=b,a=-b):")
print(" diagonal-style overlaps total 3n. Verify the count matches.")
