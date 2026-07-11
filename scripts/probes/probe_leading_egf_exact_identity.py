"""
PROBE: the EXACT generating-function identity for the char-0 LEADING term.

LANE-1 proved (and probe confirmed exact): the leading (all-distinct) char-0 energy term is
   L_r = r! * (n)_r          where (n)_r = n(n-1)...(n-r+1) = descFactorial n r.

So  L_r / (r!)^2 = (n)_r / r! = C(n, r)   (binomial coefficient).  Hence the OGF/EGF:
   sum_{r=0}^{n}  [ L_r / (r!)^2 ]  t^r   =   sum_r C(n,r) t^r   =   (1+t)^n.    (CLAIM I, exact)

This is a clean closed-form generating function for the leading char-0 energy contributions:
the leading terms ARE the binomial coefficients (rescaled by (r!)^2), summing to (1+t)^n. It crystallizes
Shaw's 'binomial EGF (1+t)^n' observation as an EXACT identity tied to the proven leading term L_r.

Test CLAIM I exactly.
"""
import math

def descfac(n, r):
    p = 1
    for j in range(r):
        p *= (n - j)
    return p

def Lr(n, r):
    return math.factorial(r) * descfac(n, r)

print("CLAIM I: sum_{r=0}^{n} [L_r/(r!)^2] t^r == (1+t)^n   (leading-term generating function):")
allI = True
for n in [4, 6, 8, 10, 12]:
    for t in [0.25, 1.0, 3.0]:
        lhs = sum((Lr(n, r) / math.factorial(r) ** 2) * t ** r for r in range(n + 1))
        rhs = (1 + t) ** n
        ok = abs(lhs - rhs) < 1e-7 * max(1, rhs)
        if not ok:
            allI = False
            print(f"  n={n} t={t}: lhs={lhs:.8g} rhs={rhs:.8g} MISMATCH")
        # also confirm coefficient-wise L_r/(r!)^2 == C(n,r)
        for r in range(n + 1):
            assert Lr(n, r) == math.factorial(r) ** 2 * math.comb(n, r), (n, r)
print(f"  CLAIM I exact (and coefficientwise L_r=(r!)^2 C(n,r)) for all tested: {allI}")
