"""The doubled extremizer 2 - X^{n/4} - X^{n/2}: does it factor nicely? At a primitive root
zeta^{n/2}=-1, zeta^{n/4}=±i, so f = 2 - (±i) - (-1) = 3 ∓ i, ||f||^2=10. We just need the per-root
evaluation f(zeta) = 3 - zeta^{n/4} (using zeta^{n/2}=-1), and ||3 - w||^2 = 10 when w^2=-1.
Check there's no clean polynomial factorization needed -- the per-root substitution suffices.
"""
import cmath
import math

for a in (2, 3, 4, 5):
    n = 2**a
    z = cmath.exp(2j * cmath.pi / n)
    ok = True
    for j in range(n):
        if math.gcd(j, n) == 1:
            zz = z**j
            f = 2 - zz**(n // 4) - zz**(n // 2)
            # claim: = 3 - zz^{n/4}  (since zz^{n/2}=-1)
            g = 3 - zz**(n // 4)
            if abs(f - g) > 1e-9 or abs(abs(f)**2 - 10) > 1e-9:
                ok = False
    print(f"n={n:2d}: f = 3 - zeta^(n/4) and ||f||^2=10 at all primitive roots: {ok}")
