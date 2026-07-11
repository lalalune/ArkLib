#!/usr/bin/env python3
"""
LANE J1c (#444): the LOAD-BEARING measurement for the S-unit/subspace lane.

Does the minimal GENUINE char-p vanishing relation length L*(n,p) among n-th
roots of unity (mu_n, n=2^mu, p = 1 mod n, p ~ n^beta) GROW with p, or is it
bounded by a small constant?

 * If L* grows ~ log p (or at least with p), the short genuine relations are
   forbidden -> the wraparound W_r vanishes for small r -> consistent with the
   floor M <= C sqrt(n log m).  But: the S-unit/CJ/DZ theory does NOT supply a
   *quantitative growth rate* that beats Johnson (it only gives the order-N
   structural constraint), so even a growing L* leaves the prize at the open
   wall (this is the honest verdict to confirm).
 * If L* is bounded, the char-0 ESS/CJ count is VACUOUS for the gap.

We use a CORRECT notion of "genuine": a signed multiset relation
   sum_i s_i h^{a_i} = 0 in F_p,  s_i in {+1,-1},  a_i in [0,n)
that is NOT 0 over Z[zeta_n].  We EXCLUDE the artifact of a single root with a
large integer coefficient (e.g. 4*h^0 + h^3 = 0): we require the relation to be
a genuine +-1 SIGNED SUBSET (each exponent used at most once with a single sign),
which is the object that actually feeds the autocorrelation/energy W_r.  (Subset,
not multiset: this is exactly the far-line incidence's vanishing-subset object.)

Also reports, for context, the LENGTH BUDGET the prize needs: a genuine relation
of length L lets the sup gain only if L <= 2r with r ~ log p; so a *lower bound*
L* >= c log p would suffice -- and we test whether the data is even consistent
with L* >= c log p.

EXACT integer arithmetic.  Meet-in-the-middle for tractable depth.
"""
import itertools
from sympy import nextprime, primitive_root

def first_primes_1_mod_n(n, lo, count):
    out = []
    p = nextprime(lo - 1)
    while len(out) < count:
        if (p - 1) % n == 0:
            out.append(p)
        p = nextprime(p)
    return out

def mu_n_powers(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]

def char0_subset_zero(signs, exps, n, half):
    """signed SUBSET (distinct exps).  zeta^{half}=-1.  0 over Z[zeta_n]?"""
    vec = [0] * half
    for s, a in zip(signs, exps):
        a %= n
        if a < half:
            vec[a] += s
        else:
            vec[a - half] -= s
    return all(v == 0 for v in vec)

def min_genuine_subset_mitm(n, p, Lcap):
    """Meet-in-the-middle over signed SUBSETS of size L (distinct exponents).
    Find min L with sum s_i h^{a_i}=0 mod p, not char-0 zero.  We split the L
    chosen positions into two halves; build a hash of partial signed sums of one
    half keyed by value mod p, look up the negation.  To keep distinctness and
    correctness we enumerate the FULL subset via combinations and signs but use
    the structural early-out; for the sizes here (n<=128, L<=10) direct signed
    subset enumeration with pruning is exact and fast enough with MITM on signs.
    """
    powers = mu_n_powers(n, p)
    half = n // 2
    from itertools import combinations, product
    for L in range(2, Lcap + 1):
        # MITM on the chosen exponent set: split signs.  We still must pick the
        # subset of exponents; do combinations(n, L) (subset, distinct) then MITM
        # over the 2^L sign vectors split into two halves of size a,b.
        a = L // 2
        b = L - a
        for combo in combinations(range(n), L):
            left_ex = combo[:a]
            right_ex = combo[a:]
            # build dict of left signed sums
            table = {}
            for ls in product((1, -1), repeat=a):
                if a and ls[0] == -1:
                    # fix global first sign +; only valid when left nonempty
                    continue
                v = 0
                for s, e in zip(ls, left_ex):
                    v = (v + s * powers[e]) % p
                table.setdefault(v, []).append(ls)
            for rs in product((1, -1), repeat=b):
                v = 0
                for s, e in zip(rs, right_ex):
                    v = (v + s * powers[e]) % p
                need = (-v) % p
                if need in table:
                    for ls in table[need]:
                        signs = ls + rs
                        if signs[0] == -1:
                            continue
                        if not char0_subset_zero(signs, combo, n, half):
                            return L, list(zip(signs, combo))
        # if nothing at this L, continue
    return None, None

import math
print("=" * 84)
print("J1c: minimal GENUINE +-1-SUBSET char-p relation length L*(n,p), exact, MITM")
print("     p = 1 mod n, p ~ n^4 (beta=4).  Multi-prime per n to test p-robustness.")
print("=" * 84)
print(f"{'n':>5} {'mu':>3} {'p':>14} {'L*':>5} {'log2 p':>8} {'~2 log2 p (depth budget 2r)':>28}")
for mu_s in (3, 4, 5, 6):
    n = 1 << mu_s
    Lcap = 8 if n <= 16 else (6 if n <= 32 else 5)
    primes = first_primes_1_mod_n(n, n ** 4, 3)
    Ls = []
    for p in primes:
        L, w = min_genuine_subset_mitm(n, p, Lcap)
        Ls.append(L)
        budget = 2 * math.log2(p)
        print(f"{n:>5} {mu_s:>3} {p:>14} {str(L):>5} {math.log2(p):>8.1f} {budget:>28.1f}")
    print(f"      -> n={n}: L* over 3 primes = {Ls}  (None means > {Lcap})")
print()
print("VERDICT logic:")
print(" * L*=None (> Lcap) at every prize-shaped prime as n grows ==> short genuine")
print("   relations are FORBIDDEN; minimal length exceeds the brute/MITM horizon and")
print("   shows NO bounded constant.  Consistent with (does not contradict) the floor,")
print("   AND consistent with DZ/CJ (the modular relations obey CJ, so are not short).")
print(" * BUT: CJ/DZ give only the ORDER-N structural constraint, NOT a quantitative")
print("   L* >= c log p.  So a growing L* here is NECESSARY-not-sufficient: the lane")
print("   confirms 'no short relation' but supplies no rate beating Johnson.")
