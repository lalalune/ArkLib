#!/usr/bin/env python3
"""
LANE J1 (#444) part C-fixed: shortest GENUINE char-p vanishing relation among
n-th roots of unity at prize-shaped (n,p), allowing the actual energy/wraparound
multiset structure (sum_i x_i = sum_j y_j mod p, x,y in mu_n, NOT equal over C).

This is the object the char-0 Evertse/ESS/Conway-Jones count CANNOT bound (char 0
theorem), and Lam-Leung-finite-field says char-p gains short relations. We measure
the shortest genuine char-p relation length L and compare to p, to the char-0 min
(=2), and to the Evertse 'depth' relevance.

EXACT integer arithmetic.
"""
import itertools
from sympy import isprime, nextprime

def first_prime_1_mod_n_at_least(n, lo):
    p = nextprime(lo-1)
    while True:
        if (p - 1) % n == 0:
            return p
        p = nextprime(p)

def prim_root(p):
    # smallest primitive root mod p
    from sympy import primitive_root
    return primitive_root(p)

def mu_n_powers(n, p):
    g = prim_root(p)
    h = pow(g, (p-1)//n, p)   # exact order n
    return [pow(h, j, p) for j in range(n)]

def shortest_genuine_charp(n, p, max_total=8):
    """
    Find shortest signed relation sum_{i} eps_i * h^{a_i} = 0 mod p with the a_i
    a MULTISET (repeats allowed) of exponents in [0,n), eps_i in {+1,-1}, total
    length L = #terms, that is NOT zero over Z[zeta_n] (genuine char-p).
    char-0 zero (Lam-Leung, 2-power): partitions into antipodal pairs
    {a,+; a+n/2,+} (zeta^a+zeta^{a+n/2}=0) or trivial cancellation {a,+; a,-}.
    Returns (L, witness) or None.
    """
    powers = mu_n_powers(n, p)
    half = n//2
    # represent a relation as a vector of net signed coefficients c[a] in Z over exponents,
    # length L = sum |c[a]| ; relation value = sum_a c[a] h^a mod p.
    # char-0 zero <=> the polynomial sum_a c[a] x^a is divisible by Phi over the
    # full cyclotomic structure; for 2-power n this means c is a Z-combination of
    # antipodal annihilators (x^a + x^{a+half}) and trivial (x^a - x^a=0 => c=0).
    # Equivalently char-0 value sum_a c[a] zeta^a = 0.  We test char-0 by computing
    # the value in Z[zeta_n] exactly via reduction mod cyclotomic (use that
    # {zeta^0..zeta^{half-1}} is a Z-basis since zeta^{half}=-1 for 2-power n).
    best=None
    # iterate over total length L
    for L in range(2, max_total+1):
        # enumerate multisets of (sign,exponent) of size L, fix lexicographic to dedupe a bit
        # we brute force signed tuples; prune by symmetry: first term sign +
        found = _search_len(powers, n, half, p, L)
        if found:
            return (L, found)
    return None

def char0_value_zero(coeff, n, half):
    """coeff: dict exponent->net integer coeff. Reduce using zeta^{half} = -1
    (true for 2-power n: zeta_n^{n/2} = -1). Basis {1,zeta,...,zeta^{half-1}}.
    Return True iff reduces to 0 vector (=> sum = 0 over Z[zeta_n])."""
    vec=[0]*half
    for a,c in coeff.items():
        a%= n
        if a < half:
            vec[a]+=c
        else:
            vec[a-half]-=c     # zeta^{a} = zeta^{a-half}*zeta^{half} = -zeta^{a-half}
    return all(v==0 for v in vec)

def _search_len(powers, n, half, p, L):
    # signed exponents; reduce search: choose multiset of exponents with signs.
    # use combinations_with_replacement on (exp) then signs.
    for exps in itertools.combinations_with_replacement(range(n), L):
        for signs in itertools.product([1,-1], repeat=L):
            if signs[0]==-1:    # fix first sign +
                continue
            val = 0
            coeff={}
            for s,a in zip(signs,exps):
                val=(val+s*powers[a])%p
                coeff[a]=coeff.get(a,0)+s
            if val==0:
                if not char0_value_zero(coeff, n, half):
                    return list(zip(signs,exps))
    return None

print("="*78)
print("Shortest GENUINE char-p relation (multiset, signed) at prize-shaped (n,p)")
print("p = smallest prime = 1 mod n with p >= n^4  (beta=4)")
print("="*78)
for mu_s in [3,4,5]:
    n=1<<mu_s
    p=first_prime_1_mod_n_at_least(n, n**4)
    res=shortest_genuine_charp(n,p,max_total=8)
    if res:
        L,wit=res
        print(f"n={n:>4} p={p:>12} (~n^4): shortest genuine char-p relation L={L}  (char-0 min=2; p={p}) => L << p")
        print(f"        witness (sign,exp): {wit}")
    else:
        print(f"n={n:>4} p={p:>12}: none up to L=8 (norm-protected at this small n)")
print()
print("If L is small and constant (independent of p) while p ~ n^4 grows, then")
print("char-p genuine relations of bounded length exist => the char-0 Evertse count")
print("(which bounds only char-0 relation TYPES) is VACUOUS for the char-p gap.")
