# probe_407_close_countlane_single_eliminant.py
#
# THE CRUX: is there a SINGLE integer D (a resultant/eliminant of the count-lane
# system) of height 2^{O(n log n)}, so that #bad primes <= log2(D) = O(n log n)?
#
# E2VanishRigidityModP proves a PER-CONFIG statement (each bad config U forces
# p <= (card U)^2+card U)^{n/2}).  Quantified over the 2^{Theta(n)} configs, that
# gives (H1) max bad prime <= 2^{O(n log n)} but NOT (H2) #distinct bad primes
# <= O(n log n).  To get (H2) you need a SINGLE integer D.
#
# The natural single integer is the ELIMINANT  G(gamma) = prod_J (gamma - sigma_J)
# (J ranging over r-subsets of mu_s, sigma_J the r-fold sumset elements) -- a MONIC
# integer polynomial in gamma whose roots are exactly Sigma_r.  Then "e_2(S) in Sigma"
# over F_p  <=>  G(e_2(S)) = 0 over F_p, and a bad prime is one where some gap-valid S
# has G(e_2(S)) != 0 while over C it would be 0.  The relevant SINGLE integer is the
# resultant of {e_1=0, e_3=0, gamma=e_2, G(gamma)} -- but that resultant is over the
# config VARIETY, NOT a single polynomial.
#
# This probe directly constructs, for n=16 (s=8, so mu_8 sumset), the integer polynomial
#   G_r(gamma) = prod over r-subsets of mu_8 of (gamma - sigma)        (sigma = r-fold sums)
# computes its HEIGHT (max |coeff|) and discriminant / its prime factors, and asks:
#   does the e2-rigidity reduce to "p does not divide a SINGLE integer related to G_r"?
# If YES (single integer of bounded height), the pigeonhole is sound.
# If the bad primes are a UNION over configs (no single bounding integer), it is NOT.

import sympy as sp
from itertools import combinations
from math import comb

def sigma_poly_and_height(n_sub, r):
    """G_r(gamma) = prod_{r-subset J of mu_{n_sub}} (gamma - sum_{zeta in J} zeta),
    as an integer polynomial in gamma (it is symmetric in mu_{n_sub}, hence integer).
    Returns (degree, log2 height, integer-coeff polynomial)."""
    gamma = sp.symbols('gamma')
    z = sp.symbols('z')
    # mu_{n_sub} via primitive root; work in cyclotomic field as algebraic combos.
    # Distinct r-fold sums over mu_{n_sub}; compute the product polynomial symbolically
    # by building it as a polynomial over the cyclotomic ring then taking the norm form.
    # Simpler: evaluate sigma_J as exact algebraic numbers and multiply (gamma - sigma_J),
    # then the result is a polynomial in gamma with algebraic coeffs that are RATIONAL
    # (symmetric) -> integer.  Use minimal polynomial route via roots.
    zeta = sp.exp(2*sp.pi*sp.I/n_sub)
    roots = []
    munsub = [sp.nsimplify(sp.cos(2*sp.pi*k/n_sub) + sp.I*sp.sin(2*sp.pi*k/n_sub)) for k in range(n_sub)]
    seen = set()
    for J in combinations(range(n_sub), r):
        s = sum(munsub[j] for j in J)
        s = sp.simplify(s)
        key = sp.nsimplify(sp.re(s)), sp.nsimplify(sp.im(s))
        roots.append(s)
    # Build polynomial prod (gamma - root); since roots are conjugate-closed and the
    # multiset is Galois-stable, coeffs are integers.  Use sp.prod then expand+nsimplify.
    G = sp.prod([gamma - sp.nsimplify(rt, rational=False) for rt in roots])
    G = sp.expand(G)
    P = sp.Poly(sp.nsimplify(G, rational=True), gamma)
    coeffs = [sp.Rational(c) for c in P.all_coeffs()]
    # round to nearest integer (they ARE integers up to float noise)
    icoeffs = [int(sp.nsimplify(c, rational=True)) if c == int(c) else int(round(float(c))) for c in coeffs]
    height = max(abs(c) for c in icoeffs) if icoeffs else 1
    return P.degree(), (float(sp.log(height, 2)) if height > 1 else 0.0), icoeffs

def distinct_sigma_count(n_sub, r):
    """exact |Sigma_r(mu_{n_sub})| over C (distinct r-fold sums), via Z[zeta] coord vectors."""
    HALF = n_sub // 2
    def coord(J):
        v = [0]*HALF
        for j in J:
            j %= n_sub
            if j < HALF: v[j] += 1
            else:        v[j-HALF] -= 1
        return tuple(v)
    return len({coord(J) for J in combinations(range(n_sub), r)})

if __name__ == '__main__':
    print("Constructing the count-lane single integer obstruction G_r(gamma) for the")
    print("sumset Sigma_r(mu_s).  The pigeonhole needs: bad primes divide a SINGLE")
    print("integer of height 2^{O(n log n)}.  Measure deg(G_r) and log2 height(G_r).\n")

    # For RS over mu_n, the worst-case subgroup is mu_s with s | n; e_2 lives in mu_{n/2}.
    # We probe the sumset over mu_s for the relevant (s, r).
    for (label, s, r) in [("n=8: mu_4 sumset r=2", 4, 2),
                          ("n=16: mu_8 sumset r=2", 8, 2),
                          ("n=16: mu_8 sumset r=3", 8, 3),
                          ("n=16: mu_8 sumset r=4", 8, 4),
                          ("n=32: mu_16 sumset r=2", 16, 2),
                          ("n=32: mu_16 sumset r=3", 16, 3)]:
        try:
            deg, logh, icoeffs = sigma_poly_and_height(s, r)
            cnt = distinct_sigma_count(s, r)
            # the "log D" pigeonhole compares #distinct primes <= log2(height) roughly,
            # but more honestly #distinct prime factors of (disc or coeffs) <= log2(height).
            nval = 2*s  # the eval group order n = 2s for this (m=2) reduction context-ish
            print(f"{label}: deg G_r = {deg}, |Sigma_r| = {cnt}, log2 height(G_r) = {logh:.2f}")
        except Exception as ex:
            print(f"{label}: FAILED ({type(ex).__name__}: {ex})")
    print("""
 KEY INTERPRETATION:
   - deg(G_r) = |Sigma_r| is the bad-scalar COUNT N_0 (the thing delta* uses).
   - height(G_r) = max|coeff| of the integer sumset polynomial.  If log2 height
     = O(n log n), then a SINGLE integer (e.g. disc(G_r) or content of the eliminant)
     of comparable height bounds ALL bad primes, and #bad primes <= log2(that integer)
     = O(n log n).
   - BUT the count-lane bad primes are NOT the roots of G_r; they are the primes where
     the SYSTEM {e_1=e_3=0, G(e_2)!=0} acquires a spurious solution.  That is an
     eliminant over the config variety, of dimension 0 but with 2^{Theta(n)} branches.
     The genuine single integer is the resultant of that eliminant -- its height is the
     real D.  This probe bounds the COMPONENT G_r; the full D-height needs the
     eliminant of the WHOLE system (see verdict).
""")
