# Probe: weight-4 antipodal-free relation norms in Z[zeta_{2^m}].
# sigma_T = sum of 4 signed roots, antipodal-free (no i with both +zeta^i and -zeta^i),
# and sigma_T != 0. Compute N(sigma_T) = Norm_{Q(zeta_n)/Q} and factor it.
# QUESTION: is there clean arithmetic structure (small prime divisors, a 2-power pattern,
#   or a characterizable "bad prime" set) for the worst-prime stratification by v2(p-1)?
import sympy as sp
from sympy import Poly, symbols, resultant, cyclotomic_poly, factorint
from itertools import combinations, product

x = symbols('x')

def norm_of_relation(m, coeffs):
    # coeffs: dict exponent -> integer coefficient (the +/- signed roots collapsed)
    # represent relation poly R(x) = sum c_e x^e, compute Res(R, Phi_{2^m})
    n = 2**m
    Phi = Poly(cyclotomic_poly(n, x), x)
    R = Poly(sum(c*x**e for e,c in coeffs.items()), x)
    if R.is_zero:
        return None
    res = resultant(R.as_expr(), Phi.as_expr(), x)
    return int(res)

def antipodal_free_weight4(m):
    # exponents in [0, 2^m), signs in {+1,-1}. weight 4 = 4 distinct (exponent) terms
    # antipodal-free: no pair (e, e+n/2) both present (that's +zeta^e and -zeta^e since zeta^{n/2}=-1)
    n = 2**m
    half = n//2
    results = []
    exps = range(n)
    seen = set()
    for combo in combinations(exps, 4):
        # check antipodal-free at the exponent level: no two exps differ by half
        bad = False
        for a,b in combinations(combo,2):
            if abs(a-b) == half:
                bad = True; break
        if bad: continue
        for signs in product([1,-1], repeat=4):
            coeffs = {}
            for e,s in zip(combo, signs):
                coeffs[e] = coeffs.get(e,0)+s
            # collapse: skip zero net (can't happen, distinct exps)
            N = norm_of_relation(m, coeffs)
            if N is None or N == 0: continue
            aN = abs(N)
            if aN in seen: continue
            seen.add(aN)
            results.append((aN, factorint(aN), combo, signs))
    return results

for m in [3,4]:
    print(f"=== m={m}, n=2^{m}={2**m} ===")
    res = sorted(antipodal_free_weight4(m))
    # show the distinct norm values and their factorizations
    vals = sorted(set(r[0] for r in res))
    print(f"  distinct |N| values ({len(vals)}): {vals[:30]}")
    # collect all odd prime divisors that appear
    odd_primes = set()
    for aN, fac, combo, signs in res:
        for pr in fac:
            if pr != 2:
                odd_primes.add(pr)
    print(f"  ODD prime divisors that appear: {sorted(odd_primes)[:40]}")
