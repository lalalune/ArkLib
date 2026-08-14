#!/usr/bin/env python3
"""
#444 lane heightgate-tight: is the closed-form a-priori height bound H_apriori(n)=(n/2-1)^(n/4)
TIGHT against the TRUE max field-norm H_true(n) = max_{R subset of mu_n, non-antipodal,
char-0 sum != 0} |N_{Q(zeta_n)/Q}( sum_{x in R} x )| ?

This is the load-bearing quantity in VanishingRootSumHeightGate.lean: the spurious-free
condition is p > H_true(n). The file uses the CRUDE a-priori closed form (n/2-1)^(n/4) and
notes it "fits" the measured values 9 (n=8), 2401 (n=16), ~2^31 (n=32). If H_true is STRICTLY
SMALLER than the a-priori bound, the prize prime p ~ n*2^128 keeps the route spurious-free for
LARGER n than the a-priori boundary n=128 -> a real frontier movement on the height wall.

EXACT integer norms. For n a 2-power, Q(zeta_n)/Q has Galois group (Z/n)^*, and for an algebraic
integer alpha = sum_{i in S} zeta^i the field norm N(alpha) = prod_{k in (Z/n)^*} sigma_k(alpha)
is a RATIONAL INTEGER. We compute it EXACTLY as the integer Resultant_t( Phi_n(t), f_S(t) ) up to
sign, where f_S(t) = sum_{i in S} t^i and Phi_n(t) = t^(n/2)+1 (n a 2-power). We use exact
integer polynomial resultant via Sylvester-free subresultant-free direct product over the n/2
primitive roots is NOT integer-exact in float, so we use the RESULTANT over Z exactly.

We compute Res(Phi_n, f_S) by the integer formula Res(Phi_n, f_S) = lc(Phi_n)^deg(f) * prod over
roots... -> instead use the polynomial-remainder (Euclidean) resultant over the RATIONALS with
Fraction for exactness, then it's an integer.

NEVER n=q-1: this is the char-0 norm (a field-universal algebraic-integer height), independent of p.
"""
from fractions import Fraction
from math import gcd
import itertools

def poly_mul(a, b):
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            r[i + j] += ai * bj
    return r

def poly_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a

def poly_divmod(a, b):
    a = [Fraction(x) for x in a]; b = [Fraction(x) for x in b]
    a = poly_trim(a[:]); b = poly_trim(b[:])
    q = [Fraction(0)] * (max(1, len(a) - len(b) + 1))
    while len(a) >= len(b) and not (len(a) == 1 and a[0] == 0):
        coeff = a[-1] / b[-1]
        deg = len(a) - len(b)
        q[deg] += coeff
        for i in range(len(b)):
            a[deg + i] -= coeff * b[i]
        a = poly_trim(a)
        if len(a) == 1 and a[0] == 0:
            break
    return q, a

def resultant(p, q):
    # Res(p,q) via Euclidean PRS with the standard degree/leading-coeff bookkeeping.
    p = poly_trim([Fraction(x) for x in p]); q = poly_trim([Fraction(x) for x in q])
    res = Fraction(1)
    sign = 1
    while len(q) > 1:
        d_p = len(p) - 1; d_q = len(q) - 1
        if d_p < d_q:
            p, q = q, p
            if (d_p % 2 == 1) and (d_q % 2 == 1):
                sign = -sign
            continue
        lc_q = q[-1]
        _, r = poly_divmod(p, q)
        r = poly_trim(r)
        d_r = len(r) - 1
        # Res(p,q) = (-1)^{deg p * deg q} lc(q)^{deg p - deg r} Res(q, r)
        if (d_p % 2 == 1) and (d_q % 2 == 1):
            sign = -sign
        res *= lc_q ** (d_p - d_r)
        p, q = q, r
    # now q is constant
    d_p = len(p) - 1
    res *= q[0] ** d_p
    return sign * res

def Phi_2power(n):
    # n-th cyclotomic poly for n a 2-power: t^(n/2) + 1
    c = [0] * (n // 2 + 1)
    c[0] = 1; c[n // 2] = 1
    return c

def fS(S, n):
    c = [0] * (max(S) + 1)
    for i in S:
        c[i] = 1
    return c

def field_norm(S, n):
    # |N_{Q(zeta_n)/Q}(sum_{i in S} zeta^i)| = |Res(Phi_n, f_S)| (n a 2-power, Phi_n monic)
    R = resultant(Phi_2power(n), fS(S, n))
    assert R.denominator == 1, f"non-integer norm {R}"
    return abs(R.numerator)

def is_antipodal(S, n):
    h = n // 2; Sset = set(S)
    if 0 in [0] and False:
        pass
    for i in S:
        if ((i + h) % n) not in Sset:
            return False
    return True

def char0_sum_is_zero(S, n):
    # sum_{i in S} zeta^i == 0 in Q(zeta_n) iff f_S(t) divisible by Phi_n(t)=t^(n/2)+1
    _, r = poly_divmod([Fraction(x) for x in fS(S, n)], [Fraction(x) for x in Phi_2power(n)])
    r = poly_trim(r)
    return all(x == 0 for x in r)

def H_true(n, cap_r=None):
    """max |N(sum_S zeta^i)| over NON-empty S subset {0..n-1} with NONZERO char-0 sum.
    (The spurious-blocking height: only nonzero-sum subsets can spuriously vanish mod p.)"""
    best = 0; argbest = None
    rng = range(1, n + 1) if cap_r is None else range(1, cap_r + 1)
    for r in rng:
        for S in itertools.combinations(range(n), r):
            if char0_sum_is_zero(set(S), n):
                continue  # zero char-0 sum: vanishes in EVERY char, not spurious
            nm = field_norm(set(S), n)
            if nm > best:
                best = nm; argbest = S
    return best, argbest

def apriori(n):
    return (n // 2 - 1) ** (n // 4)

for n in [8, 16]:
    h, arg = H_true(n)
    ap = apriori(n)
    print(f"n={n}: H_true={h}  argmax S={arg}  |  H_apriori=(n/2-1)^(n/4)={ap}  |  "
          f"ratio H_apriori/H_true={Fraction(ap, h) if h else 'inf'}  "
          f"({'TIGHT' if h == ap else 'LOOSE (apriori overestimates)' if ap > h else 'apriori UNDER (BAD)'})")

# n=32 is 2^32 subsets -> intractable to fully enumerate. Sample the structured extremal family
# (consecutive runs, which tend to maximize the norm) to get a LOWER bound on H_true(32) and
# compare to apriori(32).
print("\n# n=32 structured lower-bound probe (consecutive-run subsets, the empirical extremizers):")
n = 32
ap32 = apriori(32)
best32 = 0; arg32 = None
for r in range(1, n):
    # consecutive run starting at 0
    S = set(range(r))
    if not char0_sum_is_zero(S, n):
        nm = field_norm(S, n)
        if nm > best32:
            best32 = nm; arg32 = ('run', r)
# also single "near-antipodal-minus-one" family: full set minus one antipodal partner
print(f"n=32: H_apriori={ap32} (~2^{ap32.bit_length()-1})  structured-run max norm={best32} "
      f"(~2^{best32.bit_length()-1 if best32 else 0})  arg={arg32}")
print(f"  -> structured runs give {'WELL BELOW' if best32 < ap32 else 'AT/ABOVE'} the a-priori "
      f"bound; bit-gap = {ap32.bit_length() - (best32.bit_length() if best32 else 0)} bits")
