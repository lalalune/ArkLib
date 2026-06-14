#!/usr/bin/env python3
"""
Gate verifier for ArkLib/Data/CodingTheory/ProximityGap/MobiusCoincidenceWitness.lean.

LITERAL transcription of the Lean statements (namespace MobiusCoincidenceWitness),
checked against exact computation in Z[z]/(z^m + 1) (z := x, the universal ring for
z^m = -1 over Z; for m a 2-power this is Z[zeta_2m], faithful for the CharZero claims)
at m = 8, 16, 32, 64 (k = 3..6) plus the base m = 4 (k = 2, n = 8), AND numerically at
two split primes p = 1 (mod 2m) per m, for EVERY field element with z^m = -1 (incidence
layer) / every primitive 2m-th root (distinctness + nonvanishing layer).

Threshold audit: m = 3, 4, 5, 6 — the design claims
  * incidences + Laurent collapse at 3 <= m (so they MUST hold at m = 3, 5, 6 too);
  * exponent injectivity at 4 <= m, m != 5 (unique failure above 4 is m = 5);
  * headline/nonvanishing only at m = 2^k, k >= 2.

Cross-check: the landed anchor scripts/probes/normalizer_gap/char0_witness_check.py
computes the witness plane v = (v0,v1,v2,v3) with incidence v0*xy + v1*y + v2*x + v3 = 0.
Convention map REQUIRED: (v0,v1,v2,v3) ~ (c, d, -a, -b) up to integer content and a ring
unit +-z^t (anchor records units z^1, z^5, z^13, z^29 at n = 8,16,32,64). Any other
sign/direction match is a FAIL.

Exit 0 iff every check is green. Python3 stdlib only, exact int arithmetic.
"""

import sys
from math import gcd
from itertools import combinations

sys.path.insert(0, '/home/nubs/Git/ArkLib-moments/scripts/probes/normalizer_gap')
import char0_witness_check as anchor  # the landed ground truth

FAILURES = []
CHECKS = [0]


def report(ok, label):
    CHECKS[0] += 1
    if not ok:
        FAILURES.append(label)
        print(f"  FAIL  {label}")
    return ok


def natsub(a, b):
    """Lean ℕ truncated subtraction."""
    return a - b if a >= b else 0


# ---------------------------------------------------------------- ring layers
class NegacyclicZ:
    """Z[z]/(z^m + 1), coefficients exact ints, canonical rep = tuple of m ints."""

    def __init__(self, m):
        self.m = m
        self.zero = (0,) * m
        self.one = self.const(1)
        self.z = tuple(1 if i == 1 else 0 for i in range(m)) if m > 1 else (-1,)

    def const(self, c):
        return (c,) + (0,) * (self.m - 1)

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def neg(self, a):
        return tuple(-x for x in a)

    def smul(self, c, a):
        return tuple(c * x for x in a)

    def mul(self, a, b):
        m = self.m
        out = [0] * m
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        k = i + j
                        if k < m:
                            out[k] += ai * bj
                        else:
                            out[k - m] -= ai * bj
        return tuple(out)

    def pow(self, a, e):
        r, b = self.one, a
        while e:
            if e & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            e >>= 1
        return r

    def is_zero(self, a):
        return all(x == 0 for x in a)


class Fp:
    """Prime field F_p."""

    def __init__(self, p):
        self.p = p
        self.zero = 0
        self.one = 1

    def const(self, c):
        return c % self.p

    def add(self, a, b):
        return (a + b) % self.p

    def sub(self, a, b):
        return (a - b) % self.p

    def neg(self, a):
        return (-a) % self.p

    def smul(self, c, a):
        return (c * a) % self.p

    def mul(self, a, b):
        return (a * b) % self.p

    def pow(self, a, e):
        return pow(a, e, self.p)

    def is_zero(self, a):
        return a % self.p == 0


# --------------------------------------------------- literal Lean transcription
def cCoeff(R, z, m):
    # -z ^ (m - 1) + z - 2
    return R.add(R.add(R.neg(R.pow(z, natsub(m, 1))), z), R.const(-2))


def dCoeff(R, z, m):
    # 2 * z ^ (m - 1) - z ^ (m - 2) - z ^ 3 + z ^ 2 + z
    t = R.smul(2, R.pow(z, natsub(m, 1)))
    t = R.sub(t, R.pow(z, natsub(m, 2)))
    t = R.sub(t, R.pow(z, 3))
    t = R.add(t, R.pow(z, 2))
    return R.add(t, z)


def aCoeff(R, z, m):
    # z ^ (m - 1) - z ^ (m - 2) - z ^ 3 + 2 * z ^ 2 - 1
    t = R.pow(z, natsub(m, 1))
    t = R.sub(t, R.pow(z, natsub(m, 2)))
    t = R.sub(t, R.pow(z, 3))
    t = R.add(t, R.smul(2, R.pow(z, 2)))
    return R.sub(t, R.one)


def bCoeff(R, z):
    # -(z - 1) ^ 2
    return R.neg(R.pow(R.sub(z, R.one), 2))


def detCoeff(R, z, m):
    # aCoeff * dCoeff - bCoeff * cCoeff
    return R.sub(R.mul(aCoeff(R, z, m), dCoeff(R, z, m)),
                 R.mul(bCoeff(R, z), cCoeff(R, z, m)))


def mobius_incident_lhs(R, z, m, p1, p2):
    # cCoeff * (p.1 * p.2) + dCoeff * p.2 - aCoeff * p.1 - bCoeff
    t = R.mul(cCoeff(R, z, m), R.mul(p1, p2))
    t = R.add(t, R.mul(dCoeff(R, z, m), p2))
    t = R.sub(t, R.mul(aCoeff(R, z, m), p1))
    return R.sub(t, bCoeff(R, z))


def xExp(m):
    # ![0, 1, 2, 4, m - 1, 2 * m - 2]
    return [0, 1, 2, 4, natsub(m, 1), natsub(2 * m, 2)]


def yExp(m):
    # ![0, 1, 3, m + 2, 2 * m - 3, 2 * m - 1]
    return [0, 1, 3, m + 2, natsub(2 * m, 3), natsub(2 * m, 1)]


def witnessPoint(R, z, m, t):
    return (R.pow(z, xExp(m)[t]), R.pow(z, yExp(m)[t]))


# the six incidence theorem points, literally as stated (incident_zero..incident_five)
def theorem_points(R, z, m):
    return [
        (R.one, R.one),                                            # (1, 1)
        (z, z),                                                    # (z, z)
        (R.pow(z, 2), R.pow(z, 3)),                                # (z^2, z^3)
        (R.pow(z, 4), R.pow(z, m + 2)),                            # (z^4, z^(m+2))
        (R.pow(z, natsub(m, 1)), R.pow(z, natsub(2 * m, 3))),      # (z^(m-1), z^(2m-3))
        (R.pow(z, natsub(2 * m, 2)), R.pow(z, natsub(2 * m, 1))),  # (z^(2m-2), z^(2m-1))
    ]


# ----------------------------------------------------------------- check suites
def check_identity_layer(R, z, m, tag):
    """Layers claimed for 3 <= m, z^m = -1: generalities, Laurent collapse, the six
    incidences, witnessPoint packaging, powers-of-unity, witnessSet_eq."""
    one, zero = R.one, R.zero
    # generalities
    report(not R.is_zero(z), f"{tag}: ne_zero_of_pow_eq_neg_one (z != 0)")
    report(R.pow(z, m) == R.neg(one), f"{tag}: hypothesis z^m = -1")
    report(R.pow(z, 2 * m) == one, f"{tag}: pow_two_mul_eq_one (z^(2m) = 1)")
    a, b, c, d = aCoeff(R, z, m), bCoeff(R, z), cCoeff(R, z, m), dCoeff(R, z, m)
    zm1sq = R.pow(R.sub(z, one), 2)  # (z-1)^2
    # Laurent collapse
    report(R.mul(z, c) == zm1sq, f"{tag}: z_mul_cCoeff  z*c = (z-1)^2")
    rhs_d = R.neg(R.mul(zm1sq, R.sub(R.add(R.pow(z, 3), R.pow(z, 2)), one)))
    report(R.mul(R.pow(z, 2), d) == rhs_d,
           f"{tag}: sq_mul_dCoeff  z^2*d = -((z-1)^2*(z^3+z^2-1))")
    rhs_a = R.neg(R.mul(zm1sq, R.sub(R.sub(R.pow(z, 3), z), one)))
    report(R.mul(R.pow(z, 2), a) == rhs_a,
           f"{tag}: sq_mul_aCoeff  z^2*a = -((z-1)^2*(z^3-z-1))")
    rhs_det = R.mul(R.mul(R.pow(R.sub(z, one), 6), R.pow(R.add(z, one), 2)),
                    R.add(R.add(R.pow(z, 2), z), one))
    report(R.mul(R.pow(z, 4), detCoeff(R, z, m)) == rhs_det,
           f"{tag}: pow_four_mul_detCoeff  z^4*det = (z-1)^6*(z+1)^2*(z^2+z+1)")
    # the six incidences (theorem-literal points), exact zero
    names = ["incident_zero (1,1)", "incident_one (z,z)", "incident_two (z^2,z^3)",
             "incident_three (z^4,z^(m+2))", "incident_four (z^(m-1),z^(2m-3))",
             "incident_five (z^(2m-2),z^(2m-1))"]
    pts = theorem_points(R, z, m)
    for nm, (p1, p2) in zip(names, pts):
        report(R.is_zero(mobius_incident_lhs(R, z, m, p1, p2)), f"{tag}: {nm} == 0 exactly")
    # packaged witnessPoint: matches theorem points and is incident
    wpts = [witnessPoint(R, z, m, t) for t in range(6)]
    report(wpts == pts, f"{tag}: witnessPoint t matches incident_t point, all t")
    for t, (p1, p2) in enumerate(wpts):
        report(R.is_zero(mobius_incident_lhs(R, z, m, p1, p2)),
               f"{tag}: mobiusIncident_witnessPoint t={t}")
        report(R.pow(p1, 2 * m) == one and R.pow(p2, 2 * m) == one,
               f"{tag}: witnessPoint_pow_eq_one t={t}")
    # witnessSet_eq: image set equals the explicit literal
    explicit = {(one, one), (z, z), (R.pow(z, 2), R.pow(z, 3)),
                (R.pow(z, 4), R.pow(z, m + 2)),
                (R.pow(z, natsub(m, 1)), R.pow(z, natsub(2 * m, 3))),
                (R.pow(z, natsub(2 * m, 2)), R.pow(z, natsub(2 * m, 1)))}
    report(set(wpts) == explicit, f"{tag}: witnessSet_eq (image = explicit literal)")
    return a, b, c, d, wpts


def check_exponent_layer(m, tag, expect_inj):
    xs, ys = xExp(m), yExp(m)
    report(all(e < 2 * m for e in xs), f"{tag}: xExp_lt (all < 2m)")
    report(all(e < 2 * m for e in ys), f"{tag}: yExp_lt (all < 2m)")
    xinj = len(set(xs)) == 6
    yinj = len(set(ys)) == 6
    xinj_mod = len({e % (2 * m) for e in xs}) == 6
    yinj_mod = len({e % (2 * m) for e in ys}) == 6
    if expect_inj:
        report(xinj, f"{tag}: xExp_injective (6 distinct nats)")
        report(yinj, f"{tag}: yExp_injective (6 distinct nats)")
        report(xinj_mod, f"{tag}: x-exponents pairwise distinct mod 2m")
        report(yinj_mod, f"{tag}: y-exponents pairwise distinct mod 2m")
    else:
        report(not (xinj and yinj and xinj_mod and yinj_mod),
               f"{tag}: distinctness FAILS as designed (below threshold)")
        print(f"        {tag}: xExp={xs} yExp={ys} "
              f"(x distinct: {xinj}, y distinct: {yinj})")
    return xinj and yinj


def check_nonvanishing_layer(R, z, m, tag, char_p_artifacts=None):
    """Nonvanishing layer. In the char-0 ring Z[zeta_2m] (m 2-power) ALL of these are
    exactly the CharZero Lean claims -> gated. At char p the file claims NOTHING here
    (CharZero hypothesis); still, det/b/c/(z-1)/(z+1)/(z^2+z+1)/NONNORM are forced for
    primitive z at any split prime -> gated, while a, d and their cubic factors CAN die
    mod p -> gated only when char_p_artifacts is None (char 0 / large-prime tier),
    otherwise recorded as observed artifacts."""
    one = R.one
    a, b, c, d = aCoeff(R, z, m), bCoeff(R, z), cCoeff(R, z, m), dCoeff(R, z, m)
    det = detCoeff(R, z, m)
    report(not R.is_zero(R.sub(z, one)), f"{tag}: sub_one_ne_zero (z-1 != 0)")
    report(not R.is_zero(R.add(z, one)), f"{tag}: add_one_ne_zero (z+1 != 0)")
    report(not R.is_zero(R.add(R.add(R.pow(z, 2), z), one)),
           f"{tag}: quadratic_ne_zero (z^2+z+1 != 0)")
    cubic_a = R.sub(R.sub(R.pow(z, 3), z), one)
    cubic_d = R.sub(R.add(R.pow(z, 3), R.pow(z, 2)), one)
    if char_p_artifacts is None:
        report(not R.is_zero(cubic_a), f"{tag}: cubic_a_ne_zero (z^3-z-1 != 0)")
        report(not R.is_zero(cubic_d), f"{tag}: cubic_d_ne_zero (z^3+z^2-1 != 0)")
        report(not R.is_zero(a), f"{tag}: aCoeff_ne_zero")
        report(not R.is_zero(d), f"{tag}: dCoeff_ne_zero")
    else:
        if R.is_zero(cubic_a) or R.is_zero(a):
            char_p_artifacts.append(f"{tag}: z^3-z-1 == 0 mod p (hence aCoeff == 0)")
        if R.is_zero(cubic_d) or R.is_zero(d):
            char_p_artifacts.append(f"{tag}: z^3+z^2-1 == 0 mod p (hence dCoeff == 0)")
    report(not R.is_zero(b), f"{tag}: bCoeff_ne_zero")
    report(not R.is_zero(c), f"{tag}: cCoeff_ne_zero")
    report(not R.is_zero(det), f"{tag}: detCoeff_ne_zero (NONDEG, a*d-b*c != 0)")
    report(not (R.is_zero(b) and R.is_zero(c)), f"{tag}: not_normalizer_scaling")
    report(not (R.is_zero(a) and R.is_zero(d)), f"{tag}: not_normalizer_inversion")
    # headline literal: a*d - b*c with the SAME letters as const6_witness
    report(not R.is_zero(R.sub(R.mul(a, d), R.mul(b, c))),
           f"{tag}: const6_witness det literal a*d - b*c != 0")


def check_card_and_count(R, z, m, tag, expect_count6=True):
    wpts = [witnessPoint(R, z, m, t) for t in range(6)]
    report(len(set(wpts)) == 6,
           f"{tag}: witnessPoint_injective / witnessSet_card = 6")
    # exact incidence count over mu_2m x mu_2m (anchor's check 5)
    a, b, c, d = aCoeff(R, z, m), bCoeff(R, z), cCoeff(R, z, m), dCoeff(R, z, m)
    zp = [R.pow(z, e) for e in range(2 * m)]
    cnt = 0
    for i in range(2 * m):
        for j in range(2 * m):
            lhs = R.sub(R.sub(R.add(R.mul(c, R.mul(zp[i], zp[j])), R.mul(d, zp[j])),
                              R.mul(a, zp[i])), b)
            if R.is_zero(lhs):
                cnt += 1
    if expect_count6:
        report(cnt == 6, f"{tag}: exact incidence count over (mu_2m)^2 = 6 (got {cnt})")
    else:
        print(f"        {tag}: exact incidence count over (mu_2m)^2 = {cnt} (not gated)")
    return cnt


# -------------------------------------------------------------- anchor cross-check
def anchor_cross_check(m):
    """v from the landed anchor vs design (c,d,-a,-b): must agree up to integer
    content and a unit +-z^t. Any other sign/direction = FAIL."""
    n = 2 * m
    tag = f"anchor n={n}"
    mono, add, sub_, mul, zero, one = anchor.make_ring(n)

    def point(i, j):
        return (mono(i + j), mono(j), mono(i), one)

    v = anchor.cross_normal_ring(point(0, 0), point(1, 1), point(2, 3), sub_, mul)
    # anchor's own incidence direction: dot(v, (xy, y, x, 1)) = 0 on S(n)
    S = [(0, 0), (1, 1), (2, 3), (4, m + 2), (m - 1, 2 * m - 3), (n - 2, n - 1)]
    for (i, j) in S:
        s = zero
        for vk, pk in zip(v, point(i, j)):
            s = add(s, mul(vk, pk))
        report(s == zero, f"{tag}: anchor incidence ({i},{j})")
    # design vector in the same ring rep
    R = NegacyclicZ(m)
    z = R.z
    target = [list(cCoeff(R, z, m)), list(dCoeff(R, z, m)),
              list(R.neg(aCoeff(R, z, m))), list(R.neg(bCoeff(R, z)))]
    # remove integer content of v
    content = 0
    for vk in v:
        for co in vk:
            content = gcd(content, co)
    vred = [[co // content for co in vk] for vk in v]
    # search the unit +-z^t aligning vred with (c, d, -a, -b)
    found = None
    for sgn in (1, -1):
        for t in range(n):
            u = mono(t)
            if all([sgn * co for co in mul(vk, u)] == tk
                   for vk, tk in zip(vred, target)):
                found = (sgn, t)
                break
        if found:
            break
    if found:
        sgn, t = found
        print(f"        {tag}: v/content * ({'+' if sgn == 1 else '-'}z^{t}) "
              f"== (c, d, -a, -b)  [anchor recorded units: n=8:z^1 n=16:z^5 "
              f"n=32:z^13 n=64:z^29]")
        report(True, f"{tag}: convention map (v0,v1,v2,v3) ~ (c,d,-a,-b)")
    else:
        # diagnose: which direction DOES match? try all signed permutations of (a,b,c,d)
        report(False, f"{tag}: convention map (v0,v1,v2,v3) ~ (c,d,-a,-b) — NO unit "
                      f"aligns; sign/direction mismatch. vred={vred} target={target}")
    # proportionality minors (domain check, m is a 2-power here)
    minors_ok = True
    for (p, q) in combinations(range(4), 2):
        mm = sub_(mul(v[p], target[q]), mul(v[q], target[p]))
        if mm != zero:
            minors_ok = False
    report(minors_ok, f"{tag}: all 2x2 minors of [v ; (c,d,-a,-b)] vanish (proportional)")
    return found


# ----------------------------------------------------------------- prime helpers
def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24."""
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for w in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(w, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize(n):
    fs, q = set(), 2
    while q * q <= n:
        while n % q == 0:
            fs.add(q)
            n //= q
        q += 1
    if n > 1:
        fs.add(n)
    return fs


def find_generator(p):
    fs = factorize(p - 1)
    g = 2
    while True:
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
        g += 1


def roots_mod_p(p, m):
    """(all z with z^m = -1, all z of order exactly 2m) in F_p, p = 1 mod 2m."""
    g = find_generator(p)
    w = pow(g, (p - 1) // (2 * m), p)        # order exactly 2m
    sols = [pow(w, u, p) for u in range(2 * m) if u % 2 == 1]      # z^m = -1
    prims = [pow(w, u, p) for u in range(2 * m) if gcd(u, 2 * m) == 1]
    assert all(pow(x, m, p) == p - 1 for x in sols) and len(sols) == m
    return sols, prims


def next_split_prime(start, two_m):
    p = start + ((1 - start) % two_m)
    while not (p > start and is_prime(p) and p % two_m == 1):
        p += two_m
    return p


# ------------------------------------------------------------------------- main
def main():
    print("=" * 78)
    print("RING LAYER  Z[z]/(z^m + 1), exact integers")
    print("=" * 78)

    # main censuses + base instance (2-power m: ring = Z[zeta_2m], domain, CharZero-faithful)
    for m in [4, 8, 16, 32, 64]:
        k = m.bit_length() - 1
        tag = f"ring m={m} (n={2*m}, k={k})"
        print(f"-- {tag}" + ("  [const6_witness_eight base]" if m == 4 else ""))
        R = NegacyclicZ(m)
        check_identity_layer(R, R.z, m, tag)
        check_exponent_layer(m, tag, expect_inj=True)
        check_nonvanishing_layer(R, R.z, m, tag)
        check_card_and_count(R, R.z, m, tag, expect_count6=True)

    print("=" * 78)
    print("THRESHOLD AUDIT  m = 3, 5, 6 (design's below-threshold handling vs reality)")
    print("=" * 78)
    # m=3: incidences/collapse claimed (3<=m) MUST hold; distinctness must fail (m<4)
    for m, expect_inj in [(3, False), (5, False), (6, True)]:
        tag = f"ring m={m} (n={2*m})"
        print(f"-- {tag}")
        R = NegacyclicZ(m)
        check_identity_layer(R, R.z, m, tag)   # claimed for ALL m >= 3, incl. 5 and 6
        check_exponent_layer(m, tag, expect_inj=expect_inj)
        if m == 5:
            xs, ys = xExp(5), yExp(5)
            report(xs[3] == xs[4] == 4, "m=5: x-collision is exactly m-1 = 4 = exponent 4")
            report(ys[3] == ys[4] == 7, "m=5: y-collision is exactly m+2 = 7 = 2m-3")
        if m == 6:
            # distinct exponents -> 6 distinct points in Z[x]/(x^6+1) too (monomials)
            check_card_and_count(R, R.z, m, tag, expect_count6=False)
    # injectivity sweep: claimed iff (m = 4 or m >= 6) within m >= 3
    sweep_ok = True
    for m in range(3, 41):
        xs, ys = xExp(m), yExp(m)
        inj = len(set(xs)) == 6 and len(set(ys)) == 6
        red = all(e < 2 * m for e in xs + ys)
        injmod = len({e % (2*m) for e in xs}) == 6 and len({e % (2*m) for e in ys}) == 6
        claimed = (m == 4 or m >= 6)
        if (inj and injmod and red) != claimed:
            sweep_ok = False
            print(f"        sweep m={m}: inj={inj} injmod={injmod} red={red} "
                  f"claimed={claimed}")
    report(sweep_ok, "sweep m=3..40: distinctness holds iff m = 4 or 6 <= m "
                     "(unique failure above 4 is m = 5)")

    print("=" * 78)
    print("SPLIT-PRIME LAYER  primes p = 1 (mod 2m), all z numerically")
    print("  tier 1: small split primes — Lean-claimed checks gated; the CharZero-only")
    print("          nonvanishings (a, d, cubics) and exact count are char-p-fragile,")
    print("          recorded as artifacts (they are NOT claimed mod p).")
    print("  tier 2: census-height primes (~2^28, ~2^29; cf. anchor Hadamard < 2^56 <")
    print("          p1*p2) — EVERYTHING gated incl. full nonvanishing + count = 6.")
    print("=" * 78)
    artifacts = []
    small_table = {4: (17, 41), 8: (17, 97), 16: (97, 193), 32: (193, 257),
                   64: (257, 641)}

    def prime_suite(m, p, tier):
        assert (p - 1) % (2 * m) == 0, (m, p)
        tag0 = f"F_{p} m={m}"
        R = Fp(p)
        sols, prims = roots_mod_p(p, m)
        # primitive roots satisfy the bridge z^(2^k) = -1 (pow_two_pow_eq_neg_one)
        report(all(pow(z, m, p) == p - 1 for z in prims),
               f"{tag0}: bridge pow_two_pow_eq_neg_one on all {len(prims)} "
               f"primitive 2m-th roots")
        # incidence layer for EVERY z with z^m = -1 (the actual Lean hypothesis)
        inc_ok = pow_ok = col_ok = True
        for z in sols:
            for (p1, p2) in theorem_points(R, z, m):
                if not R.is_zero(mobius_incident_lhs(R, z, m, p1, p2)):
                    inc_ok = False
            for t in range(6):
                w1, w2 = witnessPoint(R, z, m, t)
                if pow(w1, 2 * m, p) != 1 or pow(w2, 2 * m, p) != 1:
                    pow_ok = False
            one = 1
            a, b = aCoeff(R, z, m), bCoeff(R, z)
            c, d = cCoeff(R, z, m), dCoeff(R, z, m)
            if R.mul(z, c) != R.pow(R.sub(z, one), 2):
                col_ok = False
            if R.mul(R.pow(z, 2), d) != R.neg(R.mul(
                    R.pow(R.sub(z, one), 2),
                    R.sub(R.add(R.pow(z, 3), R.pow(z, 2)), one))):
                col_ok = False
            if R.mul(R.pow(z, 2), a) != R.neg(R.mul(
                    R.pow(R.sub(z, one), 2),
                    R.sub(R.sub(R.pow(z, 3), z), one))):
                col_ok = False
            if R.mul(R.pow(z, 4), detCoeff(R, z, m)) != R.mul(R.mul(
                    R.pow(R.sub(z, one), 6), R.pow(R.add(z, one), 2)),
                    R.add(R.add(R.pow(z, 2), z), one)):
                col_ok = False
        report(inc_ok, f"{tag0}: all 6 incidences == 0 for ALL {len(sols)} z with "
                       f"z^m=-1")
        report(pow_ok, f"{tag0}: witnessPoint coords in mu_2m for all such z")
        report(col_ok, f"{tag0}: Laurent collapse identities for all such z")
        # distinctness + nonvanishing + count for every PRIMITIVE 2m-th root
        card_ok = True
        counts = set()
        for z in prims:
            wpts = [witnessPoint(R, z, m, t) for t in range(6)]
            if len(set(wpts)) != 6:
                card_ok = False
            check_nonvanishing_layer(R, z, m, f"{tag0} z={z}",
                                     char_p_artifacts=(artifacts if tier == 1
                                                       else None))
            a, b = aCoeff(R, z, m), bCoeff(R, z)
            c, d = cCoeff(R, z, m), dCoeff(R, z, m)
            zp = [pow(z, e, p) for e in range(2 * m)]
            cnt = sum(1 for i in range(2 * m) for j in range(2 * m)
                      if (c * zp[i] * zp[j] + d * zp[j] - a * zp[i] - b) % p == 0)
            counts.add(cnt)
        report(card_ok, f"{tag0}: witnessSet card 6 for all {len(prims)} primitive z")
        if tier == 2:
            report(counts == {6}, f"{tag0}: exact incidence count 6 for all primitive "
                                  f"z (got {sorted(counts)})")
        elif counts != {6}:
            artifacts.append(f"{tag0}: exact count over (mu_2m)^2 in char p = "
                             f"{sorted(counts)} (char-0 value is 6; small-p torsion "
                             f"excess, count not claimed mod p)")
        print(f"  ok    {tag0} (tier {tier}): {len(sols)} hypothesis-z, "
              f"{len(prims)} primitive z")

    for m, primes in small_table.items():
        for p in primes:
            prime_suite(m, p, tier=1)
    for m in [4, 8, 16, 32, 64]:
        p1 = next_split_prime(2 ** 28, 2 * m)
        p2 = next_split_prime(2 ** 29, 2 * m)
        for p in (p1, p2):
            prime_suite(m, p, tier=2)

    if artifacts:
        print("  -- observed char-p artifacts at tier-1 small primes (NOT Lean claims;")
        print("     these are exactly why the Lean nonvanishing layer is [CharZero]):")
        for s in artifacts:
            print(f"     * {s}")

    print("=" * 78)
    print("ANCHOR CROSS-CHECK  char0_witness_check.py conventions vs design (a,b,c,d)")
    print("=" * 78)
    for m in [4, 8, 16, 32]:
        anchor_cross_check(m)
    anchor_cross_check(64)
    # and run the anchor itself end-to-end as the final word
    for n in [8, 16, 32, 64]:
        anchor.check(n)
    report(True, "anchor script ran clean at n = 8, 16, 32, 64")

    print("=" * 78)
    if FAILURES:
        print(f"RESULT: FAIL — {len(FAILURES)} failed of {CHECKS[0]} checks")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print(f"RESULT: PASS — all {CHECKS[0]} checks green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
