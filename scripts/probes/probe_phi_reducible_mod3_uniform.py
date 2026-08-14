# PROBE (#444): is Phi_{2^m} REDUCIBLE mod 3 for ALL m >= 3 (uniform-in-m structural reason
# the prime 3 stays a CANDIDATE spur prime at every dyadic depth)?
#
# Phi_{2^m}(X) = X^{2^{m-1}} + 1 over F_3. It is irreducible mod p iff p is a "primitive root" in the
# sense ord_{2^m}(p) = deg = 2^{m-1}.  But for m >= 3 the group (Z/2^m)* is NOT cyclic (it is
# Z/2 x Z/2^{m-2}), so its exponent is 2^{m-2}, hence ord_{2^m}(p) <= 2^{m-2} < 2^{m-1} for EVERY odd p.
# => Phi_{2^m} is reducible mod EVERY odd prime for m>=3. We verify the factor structure for p=3.
#
# Distinction vs Spur: reducibility of Phi_{2^m} mod 3 is NECESSARY (Phi must split for ANY in-extension
# relation to vanish) but not sufficient for a Spur collision (also need a SHORT antipodal-free R_T to
# share a factor). So "reducible for all m" is a clean structural CANDIDATE-persistence statement, weaker
# than full Spur-persistence but uniform in m. We log both.
from sympy import Poly, symbols, cyclotomic_poly, factor_list, GF
X = symbols('X')


def ord_mod(p, mod):
    k, cur = 1, p % mod
    while cur != 1:
        cur = (cur * p) % mod
        k += 1
        if k > mod:
            return None
    return k


print("m, deg=2^(m-1), ord_2m(3), #irreducible_factors_of_Phi_mod3, reducible?")
for m in range(3, 9):
    twom = 2 ** m
    deg = twom // 2
    o = ord_mod(3, twom)
    Phi = Poly(cyclotomic_poly(twom, X), X, modulus=3)
    facs = factor_list(Phi)[1]
    nf = sum(mult for _, mult in facs)
    reducible = nf > 1
    # all irreducible factors should have degree = ord_2m(3)
    degs = sorted({f.degree() for f, _ in facs})
    print(f"m={m} deg={deg} ord={o} #factors={nf} reducible={reducible} factor_degs={degs}")
