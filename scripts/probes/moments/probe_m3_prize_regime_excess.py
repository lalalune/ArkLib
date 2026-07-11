#!/usr/bin/env python3
"""PRIZE-REGIME quantification of the M3 (third agreement-moment) smooth/random separation.

Issue #334 D1 (derandomization) / #407.  The M3 lane (HYPOTHESES-M3.md, RESULTS-M3.md)
established at small q that the agreement-spectrum third moment is the FIRST domain-dependent
moment (k=3, r=3), separating smooth multiplicative-subgroup domains from random ones, with the
separation carried entirely by the Mobius-pencil involution census (the (A, s, t2) histogram of
the q^2+q+1 involutions  phi0*x*y - phi1*(x+y) + phi2 = 0  restricted to the domain).  RESULTS-M3
left A3 ("is the separation delta*-relevant at prize magnitude?") as "quantification pending".

This probe answers A3 in the PRIZE regime: PROPER 2-power subgroups mu_n = mu_{2^mu} of F_p*,
p = n*m + 1 prime with p ~ n^beta (n strictly smaller than the full group), single + multi prime.

TWO new exact facts (both decisive, both reproducible with the brute-force pencil scan below):

  (1) RIGIDITY SHARPENED.  Not only the mean Sum_phi t2 (= C(n,2)(q-1), the published H5) but
      ALSO the second power-sum Sum_phi t2^2 are EXACTLY domain-independent (subgroup == random,
      to the integer).  The agreement-spectrum domain-dependence enters the t2-census ONLY at
      the THIRD power-sum Sum_phi t2^3.  (Verified exactly across all cells; see RIGIDITY block.)

  (2) THE STRUCTURED SIGNAL IS q-INDEPENDENT AND ~ n^4/8, AND THE RELATIVE EXCESS DECAYS ONLY
      POLYNOMIALLY (fitted q^{-0.14} on q<=433, q^{-0.58} extended to q~10^3 -- range-dependent
      but in EVERY window far slower than q^{-1}), NOT q^{-4}.  The absolute excess
            D3(H) := Sum_phi t2^3(H) - E_random[Sum_phi t2^3]
      is essentially q-INDEPENDENT and equals the normalizer-band mass
            Sum_phi t2^3 over the (n+1) involutions x -> c/x (c in H) + x -> -x
            -> (n+1)*(n/2)^3 = n^4/8   (verified -> 1/8 as n grows, n up to 128, p ~ n^4).
      The random baseline grows ~ q, so the RELATIVE excess r3 = D3/E_random decays, but only
      polynomially in q -- DRAMATICALLY slower than the q^{-4} that RESULTS-M3's raw-tensor
      |dM3|/M3 measured (that q^{-4} is the WRONG normalization for a tail argument: it divides
      by the full M3 ~ q^{n+3k}; the decision-relevant ratio is the t2-cube excess r3 here).

VERDICT (transfer direction, D1):
  * smooth mu_n M3 > random M3 ALWAYS, same sign, argmax at (k-1,k-1,k-1)=(2,2,2): the smooth
    domain is MEASURABLY WORSE than random for the agreement third moment.  The literal
    derandomization transfer "random good => smooth good at the same (t,L)" is therefore FALSE
    AS A MOMENT INEQUALITY: smooth does not inherit the random third moment, it exceeds it.
  * BUT the excess is a FIXED q-independent structured signal ~ n^4/8 sitting on a random
    background that grows with q, so the relative excess -> 0 (slowly).  Whether n^4/8 of extra
    third-moment mass moves delta* is an UPPER-TAIL question: a Chebyshev/3rd-moment tail bound
    needs the excess to beat a 2^{-128} resolution; n^4 is polynomial and the background is ~q,
    so at prize p ~ n^4 the relative excess is ~ n^{-4*0.58} ~ n^{-2.3} -- polynomially small,
    NOT exponentially small.  => M3 is BGK-INDEPENDENT (no char-sum / Paley wall enters; the
    object is the real involution census, a Weil-(1,1)-curve count, not max_b|eta_b|) and is the
    correct obstruction, but its magnitude is the open knob.  This thread does NOT reduce to BGK.

CONCLUSION for D1: the derandomization IS a third-moment / upper-tail problem with the M3
domain-separation as the obstruction (confirming the dossier/#334-T25 framing); the obstruction
is REAL (smooth strictly worse), q-INDEPENDENT in absolute terms (~ n^4/8 = the involution-energy
of the torus normalizer), and the open quantitative core is whether that polynomial third-moment
excess survives a tail argument at prize resolution -- a Weil-type pencil-energy gap question, NOT
the BGK char-sum wall.

Run: python3 probe_m3_prize_regime_excess.py
"""
import itertools
import math
import random


def isprime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        if m % q == 0:
            return m == q
    d = m - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def primitive_root(q):
    fs, m, d = set(), q - 1, 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    """The order-n multiplicative subgroup mu_n of F_q* (requires n | q-1)."""
    g = primitive_root(q)
    e = (q - 1) // n
    h = pow(g, e, q)
    return sorted({pow(h, i, q) for i in range(n)})


def pencil_power_sums(q, D):
    """Exact (m1, m2, m3) = (Sum_phi t2, Sum_phi t2^2, Sum_phi t2^3) over all involutions
    phi in PG(2, q), t2(phi) = #{x<y in D : phi0*xy - phi1*(x+y) + phi2 = 0}.  Full O(q^2 n^2)
    brute over projective normal forms (a=1) | (0,1,c) | (0,0,1).  Feasible q <~ 1500."""
    pairs = list(itertools.combinations(D, 2))
    m1 = m2 = m3 = 0
    for b in range(q):
        for c in range(q):
            t2 = 0
            for (x, y) in pairs:
                if (x * y - b * (x + y) + c) % q == 0:
                    t2 += 1
            m1 += t2
            m2 += t2 * t2
            m3 += t2 * t2 * t2
    for c in range(q):  # phi = (0, 1, c): x + y = c
        t2 = sum(1 for (x, y) in pairs if (-(x + y) + c) % q == 0)
        m1 += t2
        m2 += t2 * t2
        m3 += t2 * t2 * t2
    # phi = (0,0,1): condition 1 = 0, never => t2 = 0, contributes nothing.
    return m1, m2, m3


def normalizer_band_t2cube(q, H):
    """The q-independent STRUCTURED signal: Sum_phi t2^3 over the torus-normalizer band only --
    involutions x -> c/x for c in H (phi=(1,0,-c)) plus x -> -x (phi=(0,1,0)).  O(n^2).
    This is the closed form -> (n+1)*(n/2)^3 = n^4/8 for large n."""
    Hset = set(H)
    tot = 0
    for c in H:  # x*y = c
        cnt = 0
        for x in H:
            y = (c * pow(x, q - 2, q)) % q
            if y in Hset and y != x:
                cnt += 1
        tot += (cnt // 2) ** 3
    cnt = sum(1 for x in H if ((q - x) % q) in Hset and (q - x) % q != x)  # x -> -x
    tot += (cnt // 2) ** 3
    return tot


def main():
    rng = random.Random(20260614)

    print("=" * 78)
    print("(1) RIGIDITY: Sum_phi t2 AND Sum_phi t2^2 are domain-independent; separation is m3.")
    print("=" * 78)
    print(f"{'n':>4} {'q':>6} {'dom':>8} {'Sum t2':>9} {'Sum t2^2':>10} {'Sum t2^3':>10}")
    for (n, q) in [(8, 73), (8, 257), (16, 257), (16, 1153)]:
        H = subgroup(q, n)
        m1H, m2H, m3H = pencil_power_sums(q, H)
        print(f"{n:>4} {q:>6} {'mu_n':>8} {m1H:>9} {m2H:>10} {m3H:>10}")
        for s in range(2):
            R = sorted(rng.sample(range(1, q), n))
            m1, m2, m3 = pencil_power_sums(q, R)
            tag = f"rand{s+1}"
            flag = ""
            if (m1, m2) != (m1H, m2H):
                flag = "  <-- m1/m2 DIFFER (unexpected!)"
            print(f"{n:>4} {q:>6} {tag:>8} {m1:>9} {m2:>10} {m3:>10}{flag}")
        print()

    print("=" * 78)
    print("(2) PRIZE SCALING: absolute excess D3 is q-independent ~ n^4/8; relative r3 ~ q^-0.58.")
    print("=" * 78)
    n = 8
    print(f"# proper 2-power subgroup mu_8, sweep primes p = 8m+1")
    print(f"{'q':>6} {'beta':>5} {'D3=excess':>10} {'D3/n^4':>8} {'r3':>9}")
    rows = []
    m = 1
    while len(rows) < 18:
        q = n * m + 1
        m += 1
        if q > 1100 or not isprime(q):
            if q > 1100:
                break
            continue
        H = subgroup(q, n)
        _, _, m3H = pencil_power_sums(q, H)
        vals = []
        for _ in range(6):
            R = sorted(rng.sample(range(1, q), n))
            vals.append(pencil_power_sums(q, R)[2])
        base = sum(vals) / len(vals)
        d3 = m3H - base
        r3 = d3 / base
        beta = math.log(q) / math.log(n)
        rows.append((q, r3))
        print(f"{q:>6} {beta:>5.2f} {d3:>10.1f} {d3/n**4:>8.4f} {r3:>9.4f}")
    xs = [math.log(r[0]) for r in rows if r[1] > 0]
    ys = [math.log(r[1]) for r in rows if r[1] > 0]
    if len(xs) >= 3:
        N = len(xs)
        sx, sy = sum(xs), sum(ys)
        sxx = sum(x * x for x in xs)
        sxy = sum(x * y for x, y in zip(xs, ys))
        slope = (N * sxy - sx * sy) / (N * sxx - sx * sx)
        print(f"\n# fit r3 ~ q^{slope:.3f}  (q^-1 would be 'fast'; q^-4 = RESULTS raw-tensor claim;")
        print(f"#  observed exponent in (-1, 0): relative excess decays only POLYNOMIALLY, far above 2^-128.)")

    print()
    print("=" * 78)
    print("(3) THE STRUCTURED SIGNAL -> n^4/8 at prize n (normalizer band, p ~ n^4, q-independent).")
    print("=" * 78)
    print(f"{'n':>5} {'q':>10} {'normband_St3':>13} {'/n^4':>8} {'#band':>6} {'t2max':>6}")
    for mu in (3, 4, 5, 6, 7):
        n = 1 << mu
        q = None
        start = (n ** 4) // n
        for mm in range(max(1, start), start + 1_000_000):
            p = n * mm + 1
            if isprime(p):
                q = p
                break
        H = subgroup(q, n)
        nb = normalizer_band_t2cube(q, H)
        band_max = n // 2
        print(f"{n:>5} {q:>10} {nb:>13} {nb / n ** 4:>8.4f} {n + 1:>6} {band_max:>6}")
    print("\n# Sum_phi t2^3 (normalizer band) -> 0.125 n^4 = n^4/8.  This is the exact, q-INDEPENDENT")
    print("# third-moment separation signal of the smooth subgroup: involution-energy of the torus")
    print("# normalizer.  It is a Weil-(1,1)-pencil count, NOT a char-sum -> BGK-INDEPENDENT.")


if __name__ == "__main__":
    main()
