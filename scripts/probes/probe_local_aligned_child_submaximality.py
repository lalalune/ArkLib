#!/usr/bin/env python3
"""
#407 — WORST-CASE test of LocalAlignedChildSubmaximality (the SINGLE open Lean input).

The Lean property (Frontier/_DyadicPhaseChaining.lean:309):

  LocalAlignedChildSubmaximality (M : N -> R) (N) :=
    forall i < N, exists x y, M(i+1) = x + y  AND  x^2 + y^2 <= M(i)^2.

Intended instantiation:  M(i) = |S_{b*}(mu_{2^i})|  (worst-frequency Gauss-period sup norm),
and the split is the dyadic half-coset split
    mu_{2^{i+1}} = mu_{2^i}  U  zeta * mu_{2^i},      zeta = primitive 2^{i+1}-th root,
so for ANY frequency b,
    S_b(mu_{2^{i+1}}) = S_b(mu_{2^i}) + S_{b*zeta}(mu_{2^i})   [as complex numbers].

For the property as literally stated we need, at the b* that MAXIMIZES level i+1, to write
M(i+1) = |S_{b*}(mu_{2^{i+1}})| = x + y with x,y real and x^2+y^2 <= M(i)^2.  The natural
(and only structural) choice is x = |A|, y = |B| where A = S_{b*}(mu_{2^i}), B = S_{b* zeta}(mu_{2^i}),
PROVIDED A,B are phase-aligned so |A+B| = |A|+|B| (the cos=1 anchor).  Then the binding inequality is

    SUBMAX:   |A|^2 + |B|^2  <=  M(i)^2 = (max_b |S_b(mu_{2^i})|)^2.

This is STRICTLY STRONGER than "each child <= M(i)" (which only gives 2*M(i)^2).
It is the make-or-break.  We test it WORST-CASE: over all frequencies b (not just the max),
and report the worst violation ratio  R = (|A|^2+|B|^2) / M(i)^2.  SUBMAX holds iff R <= 1.

We ALSO report, at the level-(i+1) maximizer b*, whether the alignment cos(A,B)=1 actually holds
(needed for M(i+1)=|A|+|B|), and whether SUBMAX holds there.

ADDENDUM also tests the literal Lean def via a FREE real split: a valid (x,y) with x+y=s exists
iff s^2/2 <= M(i)^2, i.e. the literal def is EQUIVALENT to the uniform descent M(i+1) <= sqrt2*M(i).

Multi-prime, proper subgroups, prize-shaped (n | p-1, p large).  FFT-exact over F_p (no sampling).
No external deps (self-contained Miller-Rabin + primitive root).
"""
import math
import numpy as np


def is_prime(num):
    if num < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if num % q == 0:
            return num == q
    d = num - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, num)
        if x == 1 or x == num - 1:
            continue
        for _ in range(r - 1):
            x = (x * x) % num
            if x == num - 1:
                break
        else:
            return False
    return True


def prime_factors(num):
    fs = set()
    d = 2
    while d * d <= num:
        while num % d == 0:
            fs.add(d)
            num //= d
        d += 1
    if num > 1:
        fs.add(num)
    return fs


def primitive_root(p):
    fs = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    raise RuntimeError("no primitive root")


def find_prime(K, lower):
    """smallest prime p > lower with 2^K | p-1."""
    m = 1
    while True:
        cand = m * (1 << K) + 1
        if cand > lower and is_prime(cand):
            return cand
        m += 1


def gauss_vector(n, p, z):
    """indicator of mu_n = <z> as length-p real vector."""
    v = np.zeros(p)
    x = 1
    for _ in range(n):
        v[x] = 1.0
        x = (x * z) % p
    return v


def analyze(p, K, label):
    g = primitive_root(p)
    print(f"\n=== {label}: p={p}  (2^{K} | p-1, g={g}) ===")
    print(f"{'i->i+1':>8} {'n2=2^(i+1)':>10} {'M(i)':>10} {'M(i+1)':>10} "
          f"{'worstR':>9} {'SUBMAX?':>8} {'cos@b*':>8} {'submax@b*':>9}")
    worst_overall = 0.0
    any_violation = False
    for i in range(2, K):  # level i -> i+1 ; need 2^(i+1) <= 2^K
        n1 = 1 << i
        n2 = 1 << (i + 1)
        z1 = pow(g, (p - 1) // n1, p)
        z2 = pow(g, (p - 1) // n2, p)
        zeta = z2  # primitive 2^(i+1)-th root; mu_{n2} = mu_{n1} U zeta*mu_{n1}
        v1 = gauss_vector(n1, p, z1)
        Fb1 = np.fft.fft(v1)            # Fb1[b] = sum_{x in mu_{n1}} e_p(-b x)
        absF1 = np.abs(Fb1)
        Mi = absF1[1:].max()           # max over b != 0
        b_all = np.arange(p)
        bz = (b_all * zeta) % p
        A = Fb1
        B = Fb1[bz]
        Sn2 = A + B                    # = S_b(mu_{n2}) for all b  (exact half-coset identity)
        absSn2 = np.abs(Sn2)
        Mi1 = absSn2[1:].max()
        lhs = (np.abs(A) ** 2 + np.abs(B) ** 2)
        R = lhs[1:] / (Mi ** 2)
        worstR = R.max()
        worst_overall = max(worst_overall, worstR)
        submax_ok = worstR <= 1.0 + 1e-9
        if not submax_ok:
            any_violation = True
        bstar = 1 + int(np.argmax(absSn2[1:]))
        Ab, Bb = A[bstar], B[bstar]
        if abs(Ab) > 1e-9 and abs(Bb) > 1e-9:
            cosb = (Ab * Bb.conjugate()).real / (abs(Ab) * abs(Bb))
        else:
            cosb = float('nan')
        submax_bstar = (abs(Ab) ** 2 + abs(Bb) ** 2) / (Mi ** 2)
        print(f"{i:>3}->{i+1:<3} {n2:>10} {Mi:>10.4f} {Mi1:>10.4f} "
              f"{worstR:>9.4f} {'OK' if submax_ok else 'VIOLATE':>8} "
              f"{cosb:>8.4f} {submax_bstar:>9.4f}")
    print(f"  worst submax ratio over all levels/freqs: {worst_overall:.4f}  "
          f"=> {'SUBMAX SURVIVES' if not any_violation else 'SUBMAX REFUTED (>1)'}")
    return worst_overall, any_violation


def addendum():
    print("\n\n#### ADDENDUM: literal-Lean def reduces to  M(i+1) <= sqrt(2)*M(i)  ####")
    print("(min of x^2+y^2 with x+y=s is s^2/2; a valid split exists iff M(i+1)^2/2 <= M(i)^2)")
    for K, lo, lab in [(11, 2_000_000, "A"), (12, 4_000_000, "D")]:
        p = find_prime(K, lo); g = primitive_root(p)
        print(f"\n  {lab} p={p}:  {'lvl':>6} {'M(i+1)/M(i)':>12} {'<=sqrt2?':>9}")
        prevM = None
        for i in range(2, K + 1):
            n = 1 << i
            z = pow(g, (p - 1) // n, p)
            v = gauss_vector(n, p, z)
            M = np.abs(np.fft.fft(v))[1:].max()
            if prevM is not None:
                r = M / prevM
                print(f"      {i-1}->{i:<3} {r:>12.4f}    "
                      f"{'OK' if r <= math.sqrt(2)+1e-9 else 'VIOLATE':>9}")
            prevM = M


if __name__ == "__main__":
    print("LocalAlignedChildSubmaximality WORST-CASE probe  (R = (|A|^2+|B|^2)/M(i)^2, need R<=1)")
    print("FFT-exact over F_p, proper subgroups, multiple primes.")
    results = []
    for K, lo, lab in [(11, 2_000_000, "A"), (11, 3_000_000, "B"),
                       (10, 1_500_000, "C"), (12, 4_000_000, "D")]:
        p = find_prime(K, lo)
        results.append((lab, p, K) + analyze(p, K, lab))
    print("\n================ SUMMARY ================")
    for lab, p, K, w, viol in results:
        print(f"prime {lab} p={p:>9}: worst R = {w:.4f}  {'REFUTED' if viol else 'survives'}")
    if any(v for *_, v in results):
        print("\n>>> SUBMAX is REFUTED worst-case: the literal LocalAlignedChildSubmaximality"
              " input is FALSE. Log to DISPROOF_LOG.md.")
    else:
        print("\n>>> SUBMAX survives worst-case in all tested instances.")
    addendum()
