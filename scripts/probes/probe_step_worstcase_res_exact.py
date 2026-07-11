"""Pin the EXACT worst-case distinct resultant. Empirically |Res| distinct max = 8^{phi(n)/2}
attained at (0, n/4, n/2, 3n/4), i.e. fourTerm = 1 + X^{n/4} - X^{n/2} - X^{3n/4}.
Verify this is EXACTLY (2^{3/2})^{phi(n)} = sqrt(8)^{phi(n)} = 2^{3 phi(n)/2}, and identify the
closed form of THAT specific four-term: 1 + X^{n/4} - X^{n/2} - X^{3n/4}
 = (1 - X^{n/2}) + X^{n/4}(1 - X^{n/2}) = (1 + X^{n/4})(1 - X^{n/2}).
So fourTerm_worst = (1 + X^{n/4})(1 - X^{n/2}). Its resultant with Phi_n factors:
Res(Phi_n, fg) = Res(Phi_n, f) * Res(Phi_n, g). Check each factor's resultant.
"""
import sympy
from sympy import Poly, resultant, cyclotomic_poly, symbols

X = symbols('X')

for a in (2, 3, 4, 5):
    n = 2**a
    phin = sympy.totient(n)
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    f1 = Poly(1 + X**(n//4), X, domain='ZZ')        # 1 + X^{n/4}
    f2 = Poly(1 - X**(n//2), X, domain='ZZ')        # 1 - X^{n/2}
    worst = Poly((1 + X**(n//4)) * (1 - X**(n//2)), X, domain='ZZ')
    R1 = abs(int(resultant(Phi, f1)))
    R2 = abs(int(resultant(Phi, f2)))
    Rw = abs(int(resultant(Phi, worst)))
    target = 2**(3 * phin // 2)
    print(f"n={n:2d} phi={phin}: Res(Phi,1+X^(n/4))={R1}  Res(Phi,1-X^(n/2))={R2}  "
          f"product={R1*R2}  Res(worst)={Rw}  2^(3phi/2)={target}  match={Rw==target}")
