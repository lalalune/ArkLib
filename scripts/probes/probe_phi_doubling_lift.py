# PROBE (#444): does the m=3 mod-3 factorization LIFT up the tower via X -> X^2?
# Phi_{2^{m+1}}(X) = X^{2^m}+1 = (X^2)^{2^{m-1}}+1 = Phi_{2^m}(X^2)  over ANY ring.
# So if Phi_{2^m} = f*g (reducible) then Phi_{2^{m+1}}(X) = f(X^2)*g(X^2) is ALSO reducible.
# Iterating from the m=3 base (Phi_8 = (X^2+X-1)(X^2-X-1) over F_3) gives an EXPLICIT reducible
# factorization of Phi_{2^m} over F_3 for ALL m>=3 -> uniform structural candidate-persistence of p=3.
# Verify the doubling identity AND that the lifted factors are non-units, over F_3, m=3..7.
from sympy import Poly, symbols, cyclotomic_poly
X = symbols('X')

print("m, Phi_{2^{m+1}}(X) == Phi_{2^m}(X^2) over F_3 ?  lifted-factor non-unit?")
for m in range(3, 8):
    p = 3
    lhs = Poly(cyclotomic_poly(2 ** (m + 1), X), X, modulus=p)
    Phi_m = Poly(cyclotomic_poly(2 ** m, X), X, modulus=p)
    rhs = Phi_m.compose(Poly(X ** 2, X, modulus=p))   # Phi_{2^m}(X^2)
    same = (lhs - rhs).is_zero
    # lift the m=3 base factor f = X^2+X-1 by X->X^2 repeatedly to depth m
    f = Poly(X ** 2 + X - 1, X, modulus=p)
    for _ in range(m - 3):
        f = f.compose(Poly(X ** 2, X, modulus=p))
    # f should divide Phi_{2^m}
    q, r = divmod(Phi_m, f)
    divides = r.is_zero
    nonunit = f.degree() >= 1
    print(f"m={m}: Phi_2^{m+1}==Phi_2^{m}(X^2): {same};  base-factor-lift divides Phi_2^{m}: {divides}; nonunit: {nonunit} (deg {f.degree()})")
