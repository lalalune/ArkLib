#!/usr/bin/env python3
"""
PHASE-ALIGNMENT TOWER: the "cos@b*=1.0000 tower-recursive" observation is NOT a
non-average descent handle -- it is FORCED by the antipodal symmetry -1 in mu_n.
And the worst-frequency ratio |S_b*|/sqrt(n) sits INSIDE the prize envelope
C*sqrt(log(p/n)) in the prize regime (p~n^4), i.e. consistent with the sqrt law,
no prize-tension signal at accessible n.

CONTEXT (brief LIVE LANE): the fleet observed at the worst frequency b*, the two
half-coset sums S_0(b*), S_1(b*) of mu_n -> mu_{n/2} are MAXIMALLY phase-aligned
(cos ~= 1.0000) and tower-recursive, and hoped this was the non-average structural
handle a Stepanov/descent argument would exploit (since average/moment methods are
blind to it). This probe asks the load-bearing question PROBE-FIRST: WHY is cos=+1
exact, and is it a real descent structure or an artifact?

FINDING 1 (refutes the descent-handle premise). For n even, -1 = h^(n/2) in mu_n,
so mu_n is closed under x -> -x. Then for EVERY frequency b:
    S_b = sum_{x in mu_n} e_p(b x) = sum_{x in mu_n} (e_p(b x) + e_p(-b x))/2-pairing
is REAL (each x pairs with -x to give 2 cos(2pi b x/p)). Likewise mu_{n/2} contains
-1 (n/2 even for a>=2), so EACH half-coset sum S_0, S_1 is REAL too. Hence
cos(S_0, S_1) in {+1, -1} ALWAYS, for every b -- it is a sign, not a phase. cos=+1
at b* just says the two real halves have the SAME SIGN at the maximizing frequency,
which is tautologically why b* is the argmax (constructive real addition). This is
NOT a hidden non-average mechanism; it is the antipodal symmetry. The "tower-recursive
phase alignment" is the same sign statement re-applied down the 2-power tower.

FINDING 2 (the ratio lives in the prize envelope). In the prize regime p~n^4
(beta=4, log(p/n)=3 log n), the prize allows M(n) <= C sqrt(n log(p/n)) ~ C sqrt(n log n).
Observed |S_b*|/sqrt(n) vs sqrt(log2 n) and log2 n:
    n   ratio   ratio/sqrt(log2 n)   ratio/log2 n
    8   2.672   1.853                0.891
    16  3.459   2.078                0.865
    32  4.063   2.182                0.812
    64  4.816   1.966                0.803
ratio/sqrt(log2 n) rises then TURNS OVER at n=64; ratio/log2 n decreases+flattens.
=> consistent with growth ~ sqrt(log n) = the prize-allowed envelope, NOT faster.
The earlier "faster-than-sqrt-log" read at small n was a finite-size artifact.
At accessible n the single-prime worst-frequency magnitude obeys the sqrt law;
no prize-tension signal here.

HONEST SCOPE (rule 6): this does NOT close or refute the prize. It REFUTES the
phase-alignment tower as a candidate non-average descent handle (it is antipodal
symmetry, a sign not a phase), and confirms the worst-frequency ratio is inside
the prize envelope at accessible n. The deep prize wall (forall-field, n -> infinity,
worst structured bad prime, the constant C in the sqrt law) is untouched -- this
only removes one hoped-for mechanism and one false-alarm growth read.

Proper mu_n, p>=n^4, NEVER n=q-1. Pure-Python exact (cos/sin float only for the
magnitude; the REALNESS finding is exact algebra, confirmed Im=O(1e-15) machine zero).
"""
import math, cmath


def setup(a, beta=4.0):
    """Return (p, H, h): prime p~n^beta with n|p-1, mu_n = H, generator h of mu_n."""
    n = 2 ** a
    p = max(int(n ** beta), n + 1)
    while True:
        p += 1
        if (p - 1) % n:
            continue
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            break
    g = None
    for c in range(2, p):
        o = 1; y = c % p
        while y != 1:
            y = (y * c) % p; o += 1
            if o > p:
                break
        if o == p - 1:
            g = c; break
    h = pow(g, (p - 1) // n, p)
    H = [pow(h, i, p) for i in range(n)]
    assert len(set(H)) == n, "mu_n not size n"
    assert n != p - 1, "n=q-1 forbidden (full group, false positives)"
    return p, H, h


def Sb(b, group, p):
    w = 2 * math.pi / p
    r = i = 0.0
    for x in group:
        a = w * ((b * x) % p)
        r += math.cos(a); i += math.sin(a)
    return complex(r, i)


def worst_freq_full(p, H):
    """Exhaustive worst frequency (a<=5 feasible)."""
    best, bb = -1.0, 1
    for b in range(1, p):
        m = abs(Sb(b, H, p))
        if m > best:
            best, bb = m, b
    return bb, best


def worst_freq_coset(p, H, n):
    """Coset-reduced worst frequency (one rep per mu_n-coset). For a=6."""
    w = 2 * math.pi / p
    seen = bytearray(p)
    best, bb = -1.0, 1
    for b in range(1, p):
        if seen[b]:
            continue
        for u in H:
            seen[(b * u) % p] = 1
        sr = si = 0.0
        for x in H:
            ang = w * ((b * x) % p); sr += math.cos(ang); si += math.sin(ang)
        m = sr * sr + si * si
        if m > best:
            best, bb = m, b
    return bb, math.sqrt(best)


def main():
    print("FINDING 1 -- cos@b* is antipodal symmetry (S_b REAL for every b):")
    print(f"{'n':>4} {'p':>10} {'b*':>9} {'-1 in mu_n':>10} {'Im(S_full)':>12} "
          f"{'S0 real?':>9} {'S1 real?':>9} {'cos(S0,S1)':>11}")
    print("-" * 80)
    for a in [3, 4, 5]:
        n = 2 ** a
        p, H, h = setup(a)
        bs, M = worst_freq_full(p, H)
        minus1 = (pow(h, n // 2, p) == p - 1)
        sq = sorted({(x * x) % p for x in H}); sqset = set(sq)
        rep = next(x for x in H if x not in sqset)
        S0 = Sb(bs, sq, p)
        S1 = Sb(bs, [(rep * x) % p for x in sq], p)
        Sfull = Sb(bs, H, p)
        cos = (S0 * S1.conjugate()).real / (abs(S0) * abs(S1))
        print(f"{n:>4} {p:>10} {bs:>9} {str(minus1):>10} {Sfull.imag:>12.2e} "
              f"{str(abs(S0.imag) < 1e-9):>9} {str(abs(S1.imag) < 1e-9):>9} {cos:>11.4f}")

    print()
    print("FINDING 2 -- worst-frequency ratio inside the prize envelope ~sqrt(log n):")
    print(f"{'n':>4} {'p':>10} {'|S_b*|':>9} {'ratio':>7} "
          f"{'ratio/sqrt(log2n)':>18} {'ratio/log2n':>12}")
    print("-" * 64)
    data = []
    for a in [3, 4, 5]:
        n = 2 ** a
        p, H, h = setup(a)
        _, M = worst_freq_full(p, H)
        data.append((a, n, p, M))
    # a=6 via coset-reduced sweep (heavier)
    a = 6; n = 2 ** a
    p, H, h = setup(a)
    _, M = worst_freq_coset(p, H, n)
    data.append((a, n, p, M))
    for (a, n, p, M) in data:
        ratio = M / math.sqrt(n)
        print(f"{n:>4} {p:>10} {M:>9.3f} {ratio:>7.3f} "
              f"{ratio / math.sqrt(math.log2(n)):>18.3f} {ratio / math.log2(n):>12.3f}")
    print()
    print("VERDICT: cos=+1 is antipodal symmetry (sign, not phase) -> phase-alignment")
    print("tower is NOT a non-average descent handle. Ratio ~ sqrt(log n) -> inside the")
    print("prize envelope at accessible n, no prize-tension. Neither closes nor refutes")
    print("the prize; removes one hoped-for mechanism + one false-alarm growth read.")


if __name__ == "__main__":
    main()
