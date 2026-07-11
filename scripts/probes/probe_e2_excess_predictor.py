#!/usr/bin/env python3
"""
PROBE 3: nail the EXACT predictor of E_2(mu_n) excess>0.
Probe 2 showed excess=0 rows have |S+S|_Z = generic (n(n-1)/2 + n distinct sums, only
the n diagonal sums 2a plus all C(n,2) cross-sums distinct), and excess>0 rows are pinched.

For mu_n a MULTIPLICATIVE subgroup, generic integer additive energy with NO nontrivial
additive coincidence is E_2^Z = 3n^2 - 3n  (the in-tree baseline: each (a,b) with a!=b has
a+b matched only by (b,a) and one diagonal-collision pattern => 2n^2-... ; the baseline
3n^2-3n is the "additively-Sidon-like" energy of a generic n-set with no extra coincidences).

CLAIM TO TEST: excess>0  <=>  the multiplicative set mu_n has a NONTRIVIAL additive
quadruple, i.e. exists a,b,c,d in mu_n, {a,b}!={c,d}, a+b=c+d  (mod p), beyond the forced
(a,b)~(b,a) symmetry and the 2a diagonal. Equivalently the multiplicative subgroup stops
being a (mod-p) Sidon set / B_2 set.

So the onset is EXACTLY: mu_n ceases to be a Sidon set in F_p.
Print: n, p, beta, whether mu_n is Sidon (B_2) mod p, excess. They should coincide.
Also print the FIRST n (per prime) where Sidon fails = the additive-coincidence onset.
"""
import sympy, math

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def is_sidon_modp(S, p):
    # Sidon/B_2: all pairwise sums a+b (a<=b) distinct mod p
    seen = set()
    for i in range(len(S)):
        for j in range(i, len(S)):
            s = (S[i]+S[j]) % p
            if s in seen:
                return False
            seen.add(s)
    return True

def excess(S, p, n):
    from collections import Counter
    c = Counter()
    for a in S:
        for b in S:
            c[(a+b)%p] += 1
    eF = sum(v*v for v in c.values())
    return eF - (3*n*n - 3*n)

print(f"{'p':>8} {'n':>5} {'beta':>5} {'sidon?':>6} {'exc':>10} {'exc>0':>6} {'match':>6}")
print("-"*60)
for p in [193,257,769,3457,7681,12289,40961,65537,786433]:
    if not sympy.isprime(p): continue
    for a in range(3, 11):
        n = 2**a
        if (p-1) % n != 0 or n >= p: continue
        S = subgroup(p,n)
        sid = is_sidon_modp(S,p)
        exc = excess(S,p,n)
        match = (sid == (exc==0))
        print(f"{p:>8} {n:>5} {math.log(p)/math.log(n):>5.2f} {str(sid):>6} {exc:>10} {str(exc>0):>6} {str(match):>6}")
print()
print("If 'match'==True for ALL rows: excess>0  <=>  mu_n is NOT Sidon mod p.")
print("=> the E_2 excess onset = the multiplicative subgroup losing its Sidon/B_2 property.")
