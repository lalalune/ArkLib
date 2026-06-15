#!/usr/bin/env python3
"""
PROBE (#407/#444): the dyadic-tower iteration of the crossCell gap CANNOT certify CORE
even GRANTING the open BCHKS-1.12 absolute bound -- it leaks to the trivial M(n) <= n.

Context.  CrossCellShkredovBound.lean names the one open lever of the dyadic cumulant descent:
    N0(G,r) = 2*N0(H,r) + crossCell(H,zeta,r),    G = mu_n = H ⊔ zeta*H,  H = mu_{n/2},
and states the open OPEN absolute bound (= BCHKS25 Conjecture 1.12):
    CrossCellAbsoluteBound:   crossCell(H,zeta,r) * q  <=  2^r * |H|^r.
Its docstring + theorem N0_gap_of_absoluteBound give the per-level consumer
    N0(G,r) <= 2*N0(H,r) + 2^r*|H|^r / q
and ASSERT (docstring) that iterating this down the 2-power tower with q ~ n*2^128
"keeps the cross mass below the diagonal and converges to the clean closed form
 N0(G,r) ~ 2*N0(H,r) -- the closure mechanism, conditional on the open bound."
A consumer `prize_of_ShkredovSubTrivialBound` is referenced in the docstring but is NOT
present as a theorem (only the per-level N0_gap_of_absoluteBound exists).

This probe tests that asserted closure IMPLICATION exactly (char-0 bigint arithmetic on the
bound itself; independent of whether the open bound is true).  It feeds the iterated tower
upper bound on N0(G,2r) into the moment certificate
    M(n) <= min_r ( sum_{b!=0}|eta_b|^{2r} )^{1/2r},
    sum_{b!=0}|eta_b|^{2r} = q*N0(G,2r) - n^{2r}          (in-tree raw-moment identity).

Tower recursion (assuming the absolute bound at EACH level, q FIXED = prize modulus):
    T_{j+1}(r) = 2*T_j(r) + 2^r*(2^j)^r,   T_1(r) = q*N0(mu_2,r) = q*C(r,r/2) [r even else 0],
    T_j(r) := q * N0(2^j, r)  (integer-scaled, exact).

VERDICT (sound, floor-checked): granting CrossCellAbsoluteBound, the iterated certificate
floors at  M(n) <= n  (TRIVIAL), never sqrt(n*log m) (CORE) nor sqrt(n) (Johnson).
Reason: the top-level cross injection is 2^r*|H|^r = 2^r*(n/2)^r = n^r-scale, so the moment
q*N0(G,2r)-n^{2r} floors at n^{2r}, and (n^{2r})^{1/2r} = n.  The docstring's "clean closed
form / closure mechanism" claim is OVERSTATED: even with the open bound, the iteration leaks.

Soundness guard: we also evaluate the IDEAL crossCell=0 case (perfect halving = the docstring's
"clean closed form") -- it goes VACUOUS (moment <= 0) past low r, so it yields no usable bound
either.  And we floor-check every certificate against the proven floor M >= sqrt(n(q-n)/(q-1));
the "random-count" injection violates the floor (=> unsound there), confirming only the absolute
bound gives a sound certificate, and that sound certificate is trivial (= n).
"""
from math import comb
import math


def prize_params(mu):
    n = 2 ** mu
    m = 2 ** 128            # prize: m = (q-1)/n = 2^128 fixed => q ~ n*2^128
    q = n * m
    return n, m, q


def Tmu(mu, r, q, mode):
    """T_mu(r) = q*N0(2^mu, r) upper bound under the chosen cross-injection mode (exact bigint)."""
    base = comb(r, r // 2) if r % 2 == 0 else 0
    T = q * base                       # j=1 (n=2)
    for j in range(1, mu):
        H = 2 ** j
        if mode == 'ideal':            # crossCell = 0 (docstring "clean closed form", best case)
            inj = 0
        elif mode == 'abs':            # the open BCHKS-1.12 absolute bound  crossCell*q <= 2^r|H|^r
            inj = (2 ** r) * (H ** r)
        elif mode == 'rand':           # measured "random-count" form (2^r-2)|H|^r/q  (UNSOUND, see below)
            inj = (2 ** r - 2) * (H ** r)
        T = 2 * T + inj
    return T


def best_logM(mu, q, n, mode, rmax=400):
    best = None
    for r in range(1, rmax):
        twor = 2 * r
        moment = Tmu(mu, twor, q, mode) - n ** twor
        if moment <= 0:                # vacuous: no usable bound at this order
            continue
        logM = moment.bit_length() / twor    # ~ log2 M(n) upper bound
        if best is None or logM < best[1]:
            best = (twor, logM)
    return best


def main():
    print("# crossCell-tower iteration NO-GO: granting BCHKS-1.12, the iterated certificate => M(n) <= n (trivial)\n")
    print(f"{'mu':>3} {'n':>9} {'floor':>7} {'.5log2n':>8} {'CORE':>7} | "
          f"{'ideal(c=0)':>11} {'abs(BCHKS)':>11} {'rand(unsound)':>13}")
    for mu in range(3, 18):
        n, m, q = prize_params(mu)
        floor = 0.5 * math.log2(n * (q - n) / (q - 1))     # proven floor: M >= sqrt(n(q-n)/(q-1))
        half = 0.5 * math.log2(n)
        core = 0.5 * math.log2(n * math.log(m))
        bi = best_logM(mu, q, n, 'ideal')
        ba = best_logM(mu, q, n, 'abs')
        br = best_logM(mu, q, n, 'rand')

        def fmt(b):
            if b is None:
                return "vacuous"
            tag = "!" if b[1] < floor - 0.05 else ""   # floor violation => unsound certificate
            return f"{b[1]:.3f}{tag}"
        print(f"{mu:>3} {n:>9} {floor:>7.3f} {half:>8.3f} {core:>7.3f} | "
              f"{fmt(bi):>11} {fmt(ba):>11} {fmt(br):>13}")
    print("\nLEGEND: values are log2 M(n) upper bounds.  '!' = violates the proven floor M >= sqrt(n) (UNSOUND).")
    print("READ:")
    print(" - abs (open BCHKS-1.12): SOUND, floors at log2 M ~ log2 n  => M(n) <= n (TRIVIAL), never CORE/Johnson.")
    print(" - ideal (crossCell=0, the docstring 'clean closed form'): goes VACUOUS past low r => no usable bound.")
    print(" - rand (measured random-count form): VIOLATES the floor (unsound certificate) -- discarded.")
    print("VERDICT: the asserted dyadic-tower CLOSURE (conditional on the open bound) does NOT certify CORE;")
    print("         the iterated moment certificate leaks to the trivial n.  Docstring claim overstated.")


if __name__ == '__main__':
    main()
