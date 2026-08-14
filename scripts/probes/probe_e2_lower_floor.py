#!/usr/bin/env python3
"""
PROBE 4: verify rEnergy G 2 >= 3n^2 - 3n UNCONDITIONALLY (any subset G of a field, |G|=n,
0 not in G, G symmetric? NO -- mu_n need not be symmetric). Actually test the floor for
GENERAL n-subsets and for multiplicative subgroups, mod p.

E_2(G) = #{(a,b,c,d) in G^4 : a+b = c+d (mod p)}.
The GUARANTEED solutions (present for ANY set, giving the 3n^2-3n floor) are:
  (1) a+b = a+b  : (a,b,a,b) for all (a,b): n^2 solutions
  (2) a+b = b+a  : (a,b,b,a) for all (a,b): n^2 solutions
  (3) a+a = a+a counted... overlaps. The standard count of "trivial" additive quadruples
      for a Sidon set is exactly 2n^2 - n (the (a,b,a,b) and (a,b,b,a) families overlapping
      on the n diagonal a=b). But the in-tree baseline is 3n^2-3n, LARGER -- so it includes
      an extra n^2-2n structured family specific to mu_n.

So 3n^2-3n is NOT a universal floor for arbitrary sets (Sidon sets hit 2n^2-n). It is the
mu_n-specific value. Test: is 3n^2-3n a LOWER bound for multiplicative subgroups mu_n
(i.e. mu_n always has at least the extra n^2-2n structured coincidences)?  And what are they?

Hypothesis for the extra family: mu_n is closed under negation IFF -1 in mu_n IFF n even
(n=2^a, a>=1 => -1 = g^{(p-1)/2} in mu_n iff (p-1)/2 is a multiple of (p-1)/n iff n | 2...).
Actually -1 in mu_n  <=>  ord(-1)=2 divides n  <=> n even. For n=2^a, a>=1, n even => -1 in mu_n.
Then a+b=c+d has the extra family from x*mu_n = mu_n closure? Let's just COUNT and check the floor.
"""
import sympy

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def E2(S, p):
    from collections import Counter
    c = Counter()
    for a in S:
        for b in S:
            c[(a+b)%p] += 1
    return sum(v*v for v in c.values())

print(f"{'p':>8} {'n':>5} {'-1 in?':>6} {'E2':>10} {'3n^2-3n':>9} {'2n^2-n':>9} {'E2>=floor?':>10}")
print("-"*64)
for p in [193,257,769,7681,12289,40961,786433]:
    for a in range(1, 11):
        n = 2**a
        if (p-1)%n != 0 or n>=p: continue
        S = subgroup(p,n)
        e = E2(S,p)
        floor1 = 3*n*n-3*n
        floor2 = 2*n*n-n
        negin = ((p-1) in [(x) for x in S]) or (p-1 in S)
        print(f"{p:>8} {n:>5} {str(negin):>6} {e:>10} {floor1:>9} {floor2:>9} {str(e>=floor1):>10}")
print()
print("Check: is 3n^2-3n always a LOWER bound (E2 >= 3n^2-3n) for these subgroups?")
print("Also: random non-subgroup n-sets for contrast (should be able to dip to ~2n^2-n).")
