#!/usr/bin/env python3
"""
probe_407_chebotarev_alternant_n4.py  (#407)

Pin the EXACT closed form of the generalized-Vandermonde alternant for n = 4 (and
re-verify n = 3) used in `_ChebotarevAlternantThree.lean` / `_ChebotarevValuationModP.lean`.

Definitions (matching the Lean):
  minorExp ri ci i j = (-(ci[j] * ri[i]) mod p)            # canonical rep in {0,...,p-1}
  detPoly            = det( X^{minorExp i j} )  in  Z[X]
  alternant          = (taylor 1 detPoly).coeff (C(n,2))   in  Z
                     = sum_sigma sign(sigma) * C(s_sigma, C(n,2)),  s_sigma = sum_i e_{i,sigma(i)}
  alternantModP      = alternant mod p

n = 3 PROVEN closed form (every p):   6*alternantModP = -3 * V_r * V_c
  V_r = (r0-r1)(r0-r2)(r1-r2),  V_c = likewise   (all mod p)
  i.e.  alternantModP = (-1/2) * V_r * V_c.

GOAL for n = 4: find integer constants k_n, c_n with
  k_n * alternantModP = c_n * V_r * V_c   over ZMod p   (V_* the full Vandermonde diff product)
and report the ratio alternant / (V_r * V_c) as an element of ZMod p (when V_r*V_c invertible).
We do this by a FULL census over small primes and (for larger primes) a sample.
"""

import itertools
from math import comb
from fractions import Fraction


def perms_with_sign(n):
    out = []
    for perm in itertools.permutations(range(n)):
        # sign via inversion count
        inv = 0
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    inv += 1
        out.append((perm, (-1) ** inv))
    return out


def vandermonde(vals, p):
    n = len(vals)
    prod = 1
    for i in range(n):
        for j in range(i + 1, n):
            prod = (prod * ((vals[i] - vals[j]) % p)) % p
    return prod


def alternant_modp(ri, ci, p, n, PS):
    """integer alternant reduced mod p (as defined: coeff of (X-1)^{C(n,2)})."""
    m = comb(n, 2)
    e = [[(-(ci[j] * ri[i])) % p for j in range(n)] for i in range(n)]
    total = 0  # accumulate integer alternant, then mod p at the end
    for perm, sgn in PS:
        s = sum(e[i][perm[i]] for i in range(n))
        total += sgn * comb(s, m)
    return total % p


def injective_funcs(n, p):
    return itertools.permutations(range(p), n)


def census_ratio(n, p, sample=None, seed=0):
    """Return set of (alternant mod p, V_r*V_c mod p) over injective ri,ci; and
    the ratio alternant/(VrVc) over invertible cases.
    If `sample` is set, draw that many random injective (ri,ci) pairs instead of full census."""
    import random
    PS = perms_with_sign(n)
    ratios = set()
    zero_vrc_with_nonzero_alt = 0
    if sample is None:
        funcs = list(injective_funcs(n, p))
        pairs_iter = ((ri, ci) for ri in funcs for ci in funcs)
    else:
        rng = random.Random(seed)
        def draw():
            return tuple(rng.sample(range(p), n))
        pairs_iter = ((draw(), draw()) for _ in range(sample))
    for ri, ci in pairs_iter:
        Vr = vandermonde(ri, p)
        Vc = vandermonde(ci, p)
        a = alternant_modp(list(ri), list(ci), p, n, PS)
        VrVc = (Vr * Vc) % p
        if VrVc != 0:
            inv = pow(VrVc, p - 2, p)
            ratios.add((a * inv) % p)
        else:
            if a != 0:
                zero_vrc_with_nonzero_alt += 1
    return ratios, zero_vrc_with_nonzero_alt, []


def main():
    print("=== n=3 sanity (PROVEN: alternant = -1/2 * Vr*Vc, i.e. ratio = -inv(2)) ===")
    for p in [3, 5, 7, 11, 13]:
        ratios, zbad, _ = census_ratio(3, p)
        if p >= 5:
            expected = (-pow(2, p - 2, p)) % p  # -1/2 mod p
        else:
            expected = None
        print(f"  p={p:3d}  ratios(alt/VrVc)={sorted(ratios)}  "
              f"expected(-1/2)={expected}  zero-VrVc&nonzero-alt={zbad}")

    print()
    print("=== n=4 census: ratio alternant/(Vr*Vc) over injective pairs ===")
    # full census feasible only for p=5,7 (P(p,4)^2 functions); sample beyond
    for p in [5, 7]:
        ratios, zbad, _ = census_ratio(4, p)
        print(f"  p={p:3d}  #distinct ratios={len(ratios)}  ratios={sorted(ratios)}  "
              f"zero-VrVc&nonzero-alt={zbad}  (FULL)", flush=True)
    for p in [11, 13]:
        ratios, zbad, _ = census_ratio(4, p, sample=6000)
        print(f"  p={p:3d}  #distinct ratios={len(ratios)}  ratios={sorted(ratios)}  "
              f"zero-VrVc&nonzero-alt={zbad}  (SAMPLE 6000)", flush=True)

    print()
    print("=== n=4: pin the rational ratio c_4/k_4 from the per-prime ratio r_p ===")
    # If alternant = (c/k) * Vr*Vc with c/k a fixed rational, then r_p = (c/k) mod p for all p.
    # Recover the rational via CRT-style guess: try small denominators.
    rp = {}
    # full census for p=5,7; sampling for larger ones (to keep it fast)
    full = {5, 7}
    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if p in full:
            ratios, zbad, _ = census_ratio(4, p)
        else:
            ratios, zbad, _ = census_ratio(4, p, sample=3000)
        if len(ratios) == 1:
            rp[p] = next(iter(ratios))
        else:
            rp[p] = ("MULTI", sorted(ratios))
        print(f"    p={p:3d}: ratio={rp[p]}  (zero-VrVc&nonzero-alt={zbad})", flush=True)
    print("  per-prime ratio r_p (alt/VrVc):", rp, flush=True)

    # try to match r_p = c/k mod p for small c,k
    print()
    print("=== match r_p to a fixed rational c/k (search |c|<=40, 1<=k<=40) ===")
    primes = [p for p in rp if not isinstance(rp[p], tuple)]
    best = []
    for k in range(1, 41):
        for c in range(-40, 41):
            if c == 0:
                continue
            ok = True
            for p in primes:
                if k % p == 0:
                    ok = False
                    break
                lhs = (c * pow(k, p - 2, p)) % p
                if lhs != rp[p]:
                    ok = False
                    break
            if ok:
                g = abs(__import__("math").gcd(c, k))
                best.append((c // g, k // g))
    best = sorted(set(best), key=lambda t: (t[1], abs(t[0])))
    print("  candidate rationals c/k matching ALL census primes:", best[:10])
    if best:
        c, k = best[0]
        print(f"  => alternant = ({c}/{k}) * Vr*Vc   i.e.   {k}*alternant = {c}*Vr*Vc")


if __name__ == "__main__":
    main()
