#!/usr/bin/env python3
"""
#444 G1/G2 bridge — the DEGREE LAW of the descent quadform R = Pp^2 - X*Qp^2.

My pushed kernel _DoorIVZLagrangeBound proved Z <= natDegree R for R = Pp^2 - X*Qp^2.
The NEXT rung (un-locked, deconflicted: _DichMechFiberNoGo has natDegree_X_mul_O_sq_le and a
no-go on isoP, but NOT the clean Z-consumer chain) is the explicit degree law:

   deg R = deg(Pp^2 - X*Qp^2) <= max( 2*deg Pp , 1 + 2*deg Qp )  <=  1 + 2*max(deg Pp, deg Qp).

so the non-symmetric descent Z-term is exponent-controlled:  Z <= 1 + 2*max(deg Pp, deg Qp).
This connects G1 (the Z bound) to G2 (worst-word exponent): a weight-w word with max half-degree d
gives Z <= 2d+1, and the worst d ~ n/4 mid-exponent matches the empirical worst word x^{n/4}+1.

This probe confirms the degree law numerically (deg over a field, generic Pp,Qp) and checks the
end-to-end inequality Z(B) <= 1 + 2*max(deg Pp, deg Qp) on actual subgroup bases B = mu_N.

probe-first, EXACT mod p, proper 2-power mu_n, p>>n^3, structured primes, never n=q-1.
"""
from sympy import isprime, primitive_root
import random


def find_prime(n, beta=4):
    a = n.bit_length() - 1
    target = n ** beta
    mu = a + 3
    while True:
        base = 1 << mu
        k = (target // base) | 1
        for _ in range(20000):
            p = k * base + 1
            if p > target and isprime(p) and (p - 1) % n == 0 and (p - 1) // n > 1:
                return p
            k += 2
        mu += 1


def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, j, p) for j in range(n)]


def polydeg(coeffs, p):
    d = -1
    for e, c in coeffs.items():
        if c % p != 0 and e > d:
            d = e
    return d


def evalpoly(coeffs, y, p):
    s = 0
    for e, c in coeffs.items():
        s = (s + c * pow(y, e, p)) % p
    return s % p


def quadform_coeffs(Pp, Qp, p):
    """R = Pp^2 - X*Qp^2 as exp->coef."""
    R = {}
    # Pp^2
    items = list(Pp.items())
    for i, (e1, c1) in enumerate(items):
        for (e2, c2) in items:
            R[e1 + e2] = (R.get(e1 + e2, 0) + c1 * c2) % p
    # - X*Qp^2
    qitems = list(Qp.items())
    for (e1, c1) in qitems:
        for (e2, c2) in qitems:
            e = 1 + e1 + e2
            R[e] = (R.get(e, 0) - c1 * c2) % p
    return R


def main():
    print("=" * 78)
    print("#444 G1/G2 — descent quadform degree law:  deg R <= 1 + 2*max(deg Pp, deg Qp)")
    print("=" * 78)
    random.seed(11)
    print(f"  {'n':>4} {'p':>12} {'degPp':>5} {'degQp':>5} {'degR':>5} {'1+2max':>7} {'degLawOK':>8} {'Z(B)':>5} {'Z<=1+2max':>9}")
    okall = True
    for n in [8, 16, 32, 64]:
        p = find_prime(n)
        mun = subgroup(p, n)
        muN = sorted(set(pow(x, 2, p) for x in mun))
        for _ in range(6):
            dP = random.randint(0, n // 2)
            dQ = random.randint(0, n // 2)
            Pp = {e: random.randrange(1, p) for e in range(dP + 1)}
            Qp = {e: random.randrange(1, p) for e in range(dQ + 1)}
            degP = polydeg(Pp, p)
            degQ = polydeg(Qp, p)
            R = quadform_coeffs(Pp, Qp, p)
            degR = polydeg(R, p)
            bound = 1 + 2 * max(degP, degQ)
            lawok = degR <= bound
            # Z(B) = #{y in muN : R(y)=0}
            Z = sum(1 for y in muN if evalpoly(R, y, p) == 0)
            zok = Z <= bound
            if not lawok or not zok:
                okall = False
            print(f"  {n:>4} {p:>12} {degP:>5} {degQ:>5} {degR:>5} {bound:>7} {str(lawok):>8} {Z:>5} {str(zok):>9}")
    print(f"\n  => degree law + Z<=1+2max(degP,degQ): {'ALL HOLD' if okall else 'VIOLATION'}")
    print("  (confirms the exponent-controlled chain Z <= deg R <= 1 + 2*max(deg Pp, deg Qp),")
    print("   bridging the locked Z<=degR Lagrange bound to the G2 worst-word exponent dichotomy.)")


if __name__ == "__main__":
    main()
