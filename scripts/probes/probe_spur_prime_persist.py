# PROBE (#444): does a spurious-collision prime PERSIST up the dyadic tower mu_{2^m}?
#
# The char-p energy splits E_r = E_r^(0) + Spur_r(p); Spur counts antipodal-free short relations T
# (signs +-1, |T| <= 2r) whose cyclotomic norm N(sigma_T) is divisible by p, decidably:
#   p bad at depth m  <=>  Phi_{2^m} and some relation poly R_T are NOT coprime in F_p[X]
#   (i.e. gcd(Phi_{2^m}, R_T) has degree >= 1: they share a root in F_p-bar).
#
# QUESTION: a prime bad at m=3 (e.g. p=3) -- is it still bad at m=4?  Do NEW primes enter?
# This is the "Chebotarev persistence" mechanism the prize argument assumes; here we test it
# CONCRETELY at the lowest rungs (decidable F_p[X] gcd, no n=q-1, antipodal-free only).
#
# RESULT (weight<=3):
#   m=3 p=3 ord_16(3)=2 -> bad, witness (3, (0,1,2), (1,1,-1)) = 1 + z - z^2
#   m=4 p=3 ord_16(3)=4 -> bad, witness (3, (0,2,4), (1,1,-1)) = 1 + z^2 - z^4   <-- PERSISTS
#   m=3 p=5 -> spur-free ;  m=4 p=5 -> spur-free
#   m=3 p=7 -> spur-free ;  m=4 p=7 -> bad, (3,(0,1,2),(1,1,-1))   <-- NEW prime enters
# CONCLUSION: bad primes persist up the tower AND new bad primes enter -> the bad-prime set does not
# shrink (consistent with Spur growing).  The m=4 p=3 witness 1+z^2-z^4 is formalized in
# SpurPrimePersistTower.lean (Phi_16 = (X^4+X^2-1)(X^4-X^2-1) shares X^4-X^2-1 with 1+X^2-X^4 over F_3).
import itertools
from sympy import Poly, symbols, cyclotomic_poly, gcd as sgcd
X = symbols('X')


def ord_mod(p, mod):
    k = 1
    cur = p % mod
    while cur != 1:
        cur = (cur * p) % mod
        k += 1
        if k > mod:
            return None
    return k


def spur_witness(m, p, wmax):
    """Smallest antipodal-free relation (weight<=wmax, signs +-1, first sign +1) that is
       NOT coprime with Phi_{2^m} over F_p, or None."""
    twom = 2 ** m
    half = twom // 2
    Phi = Poly(cyclotomic_poly(twom, X), X, modulus=p)
    idxs = list(range(twom))
    for w in range(2, wmax + 1):
        for T in itertools.combinations(idxs, w):
            S = set(T)
            if any((i + half) % twom in S for i in T):   # antipodal-free
                continue
            for signs in itertools.product([1, -1], repeat=w - 1):
                sg = [1] + list(signs)
                coeffs = {}
                for s, i in zip(sg, T):
                    coeffs[i] = coeffs.get(i, 0) + s
                deg = max(coeffs)
                clist = [0] * (deg + 1)
                for i, c in coeffs.items():
                    clist[deg - i] = c
                R = Poly(clist, X, modulus=p)
                if R.is_zero:
                    continue
                if sgcd(Phi, R).degree() >= 1:
                    return (w, T, tuple(sg))
    return None


if __name__ == "__main__":
    print("m, p, ord_2m(p), spur(weight<=3) witness")
    for p in [3, 5, 7]:
        for m in [3, 4]:
            twom = 2 ** m
            o = ord_mod(p, twom)
            w = spur_witness(m, p, 3)
            print(f"m={m} p={p} ord={o}  ->  {w}")
        print()
