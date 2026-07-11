#!/usr/bin/env python3
"""
Probe for C05 (Freiman 3k-4 Rigidity of the Bad-Coset).

CONJECTURE C05 claims: the bad set B_w in F_p has small doubling
  |B_w + B_w| <= 3|B_w| - 4
because each antipodal mu_d-coset is an "arithmetic progression in the
cyclotomic exponent", so Freiman's 3k-4 theorem confines B_w to a rank-1
GAP forcing |B_w| = n/gcd(b-a,n) and delta* past Johnson.

THE TEST. The bad set / its building blocks are (single-codeword) bad-alpha
orbits, which by the in-tree orbit-count law are exactly cosets of a cyclic
subgroup <mu_n^{b-a}> of F_p^*, i.e. GEOMETRIC progressions / multiplicative
cosets in F_p, NOT additive arithmetic progressions.

An AP in the EXPONENT j (i.e. {j0, j0+s, j0+2s,...}) maps under j -> zeta^j
to a GEOMETRIC progression {zeta^{j0}, zeta^{j0} r, zeta^{j0} r^2, ...} with
r = zeta^s in F_p^*. Freiman 3k-4 is a statement about ADDITIVE doubling
|A+A|. A geometric progression / multiplicative coset has LARGE additive
doubling in general (close to |A|^2/2, the Sidon-like max), NOT 3|A|-4.

We measure additive doubling |B+B| for the actual bad-alpha cosets over
proper subgroups mu_n with p prime, p >> n^3, NEVER n=p-1.
"""
import sympy
from math import gcd

def find_p_and_subgroup(n, beta_min_pow=3):
    """p prime, p >> n^beta (here n^3..n^4), n | p-1, mu_n proper subgroup."""
    # want p > n^(beta), n < p^{1/4} prize-ish; use p ~ n^4
    target = n**4
    m = target // n
    while True:
        p = m * n + 1
        if sympy.isprime(p) and p > 100 * n**3:
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)   # primitive n-th root of unity
            mu = [pow(z, j, p) for j in range(n)]
            assert len(set(mu)) == n, "mu_n not size n"
            assert p - 1 != n, "would be full group -- forbidden"
            return p, z, mu
        m += 1

def additive_doubling(S, p):
    """|S+S| in F_p."""
    Sset = set(S)
    sums = set((a + b) % p for a in Sset for b in Sset)
    return len(sums)

def coset_of_subgroup(z, n, a, b, p):
    """
    The single-codeword bad-alpha set for pencil (a,b):
    B = { -z^{j a} * (z^{j b})^{-1} : j in 0..n-1 }
      = { -z^{j(a-b)} : j }  -- a multiplicative coset of <z^{a-b}> times (-1).
    Orbit size S = n / gcd(b-a, n).
    """
    elts = set()
    for j in range(n):
        zja = pow(z, (j * a) % n, p)
        zjb = pow(z, (j * b) % n, p)
        inv = pow(zjb, p - 2, p)
        alpha = (-(zja) * inv) % p
        elts.add(alpha)
    return elts

print("=== C05 probe: additive doubling of the bad-alpha multiplicative coset ===")
print("Freiman 3k-4 would require |B+B| <= 3|B|-4. Geometric/mult coset => large.\n")
print(f"{'n':>5} {'p':>14} {'(a,b)':>10} {'gcd':>4} {'|B|':>5} {'|B+B|':>7} "
      f"{'3|B|-4':>7} {'Freiman?':>9} {'|B|(|B|+1)/2':>13}")

for n in [16, 32, 64, 128]:
    p, z, mu = find_p_and_subgroup(n)
    # deployment directions from B2 door: (k,3k),(k,2k),(3k/2,2k) with k=n/4
    k = n // 4
    pencils = [(k, 3*k), (k, 2*k), (3*k//2, 2*k), (1, 2), (1, n//2)]
    for (a, b) in pencils:
        if a == b: continue
        d = gcd((b - a) % n, n)
        S = n // d  # orbit size = |B|
        B = coset_of_subgroup(z, n, a, b, p)
        dbl = additive_doubling(B, p)
        bound = 3 * len(B) - 4
        ok = dbl <= bound
        sidon_max = len(B) * (len(B) + 1) // 2
        print(f"{n:>5} {p:>14} {str((a,b)):>10} {d:>4} {len(B):>5} {dbl:>7} "
              f"{bound:>7} {str(ok):>9} {sidon_max:>13}")

print()
print("=== Part 2: the conflation -- exponent additive AP vs F_p additive set ===")
print("In the EXPONENT group Z/n, the bad set IS {j(a-b) mod n : j} = a coset of")
print("a subgroup = an AP with step (a-b). It has SMALL doubling THERE (it's a")
print("subgroup-coset of Z/n). But Z/n doubling is TRIVIAL: a subgroup H has")
print("|H+H|=|H|, |H|<=|H|<3|H|-4 trivially. This pins |B|=n/gcd in Z/n -- but")
print("that is EXACTLY the orbit-count law (S=n/gcd(b-a,n)) ALREADY in-tree,")
print("which the B2-door file states is CIRCULAR: '#bad=O(n) is the prize floor")
print("itself' and N_pencil (the multiplicity) is what is actually open.")
print()
print("Freiman in Z/n on a subgroup gives |B|=n/gcd. Orbit law: I=N*S, S=n/gcd.")
print("Freiman pins S, NOT N. delta* past Johnson needs N (=N_pencil) bounded,")
print("which is the open BGK count. Freiman says nothing about N.")
print()

# Demonstrate: the exponent-AP doubling is trivially small (subgroup) but it
# only fixes S, and the I = N*S decomposition's N is untouched.
from collections import Counter
def exponent_set_doubling(n, a, b):
    d = gcd((b-a) % n, n)
    H = set((j*(a-b)) % n for j in range(n))  # the exponent coset
    dbl = set((x+y) % n for x in H for y in H)
    return len(H), len(dbl), n//d

print(f"{'n':>5} {'(a,b)':>10} {'|H_exp|':>8} {'|H+H|_Z/n':>11} {'n/gcd':>6} {'subgrp?':>8}")
for n in [16,32,64]:
    k=n//4
    for (a,b) in [(k,3*k),(k,2*k),(1,2)]:
        if a==b: continue
        h,dbl,s = exponent_set_doubling(n,a,b)
        print(f"{n:>5} {str((a,b)):>10} {h:>8} {dbl:>11} {s:>6} {str(dbl==h):>8}")
