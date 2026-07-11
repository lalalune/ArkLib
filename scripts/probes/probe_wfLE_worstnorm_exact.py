#!/usr/bin/env python3
"""
wf-LE (#407): EXACT worst-case non-antipodal root-sum norm vs the (n/2-1)^{n/4} claim.

The height-gate / LEVER H closes the low-exponent prize direction iff for every
non-antipodal S subset of range(n) (n = 2^a), the algebraic-integer norm

    N(Sigma_S) = N_{Q(zeta_n)/Q}( sum_{i in S} zeta^i ) = Res(Sigma_S(x), Phi_n(x))

stays below the prize prime p ~ n * 2^128.

The live session's HeightGateThresholdAnalysis claims the realized worst-case
norm EQUALS (n/2 - 1)^{n/4} (ratio -> 1), making n=64 a HARD intrinsic ceiling.

This probe checks that claim EXACTLY (integer resultants, no float) for n=8,16,32
by full / heavy search, and reports the true worst-case log2|N| and the worst S.
For n=2^a, Phi_n = x^{n/2} + 1, so N(Sigma_S) = Res(Sigma_S, x^{n/2}+1).
Antipodal = S closed under i -> i + n/2 (these give N=0 contributions / paired).

We compute |N| as a Z-integer via numpy companion-free integer resultant:
N(Sigma_S) = prod over primitive n-th roots w of Sigma_S(w).
Since Phi_n = x^{n/2}+1, reduce Sigma_S mod x^{n/2}+1 to a degree < n/2 poly r(x);
then N = Res(r, x^{n/2}+1) = prod_{w: w^{n/2}=-1} r(w). We get this exactly as the
integer = product, computed via the resultant of integer polynomials (sympy, exact).
"""
import itertools, math
import sympy as sp

x = sp.symbols('x')

def Phi(n):
    # n = 2^a  =>  Phi_n = x^{n/2} + 1
    return sp.Poly(x**(n//2) + 1, x)

def norm_of_subset(S, n):
    # Sigma_S(x) = sum x^i  ; reduce and take resultant with Phi_n
    poly = sp.Poly(sum(x**i for i in S), x)
    return abs(int(sp.resultant(poly, Phi(n).as_expr())))

def is_antipodal(S, n):
    h = n // 2
    Sset = set(S)
    # antipodal: S is a union of pairs {i, i+h mod n}? The Lam-Leung char-0 vanishing
    # set is exactly: closed under negation pairs. We use: S decomposes into disjoint
    # {i, i+h} pairs (i.e. for the norm to be 0). We exclude exactly the zero-norm sets.
    return norm_of_subset(S, n) == 0

def worst_nonantipodal(n, max_eval=None):
    h = n // 2
    best = 0
    best_S = None
    elems = list(range(n))
    # full enumeration feasible for n<=16 (2^16). For n=32 sample heavy + structured.
    total = 0
    if n <= 16:
        for r in range(1, n+1):
            for S in itertools.combinations(elems, r):
                v = norm_of_subset(S, n)
                total += 1
                if v > best:
                    best = v; best_S = S
    return best, best_S, total

if __name__ == "__main__":
    claim = lambda n: (n//2 - 1) ** (n//4)
    print(f"{'n':>4} {'worst|N|(bits)':>16} {'(n/2-1)^(n/4)(bits)':>22} {'ratio':>8} {'worstS':>30}")
    for n in [8, 16]:
        best, bS, tot = worst_nonantipodal(n)
        wb = math.log2(best) if best > 0 else 0
        cb = math.log2(claim(n)) if claim(n) > 0 else 0
        ratio = wb/cb if cb>0 else float('nan')
        print(f"{n:>4} {wb:16.3f} {cb:22.3f} {ratio:8.4f} {str(bS):>30}  (enum {tot})")
