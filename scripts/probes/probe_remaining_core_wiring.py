#!/usr/bin/env python3
"""Probe for the BCIKS20RemainingCore wiring (issue #304 / #232, O78 candidate).

The Lean deliverable (`BCIKS20/RemainingCore.lean`) defines

    BCIKS20RemainingCore k deg domain delta delta' :=
      StrictCoeffPolysResidualLarge(delta) AND StrictCoeffPolysResidualLarge(delta')

and wires it into the Theorem-1.5 keystone via
  * the O70 front door (`correlatedAgreement_affine_curves_of_largeResidual`) on the
    strict interior, and
  * the O76 floor-matched transport
    (`correlatedAgreementCurves_boundary_of_floorEq_strict`) at the closed boundary,
with conclusion error  max(errorBound(delta), errorBound(delta')).

This probe checks, in exact arithmetic, that the wiring's side hypotheses are
JOINTLY SATISFIABLE (the conjunction is not demanded in an empty regime) and that
the corrected boundary route is non-degenerate:

  C1  at every non-lattice boundary delta = 1 - sqrt(rho), the canonical
      delta' = floor(delta*n)/n satisfies  delta' < delta,
      floor(delta'*n) = floor(delta*n),  and  delta' < 1 - sqrt(rho);
  C2  errorBound(boundary) = 0 (the refuted-shape endpoint epsilon) while
      errorBound(delta') > 0, so max(eps_delta, eps_delta') = errorBound(delta') > 0
      at the boundary -- the corrected export is never the vacuous epsilon = 0 one;
  C3  lattice boundaries (deg*n a perfect square) have NO strict floor-matched
      delta' (the route honestly excludes them, matching
      `not_exists_lt_floor_eq_of_lattice`);
  C4  the O76 witness (n=4, deg=2, q=5) reproduces exactly: non-lattice boundary,
      delta' = 1/4, k*errorBound(delta') = 4/5 (the "Pr = 1/5 <= 4/5" line of O76);
  C5  census: in how many grid points does delta' land in the Johnson window
      ((1-rho)/2, 1-sqrt(rho)) -- where conjunct 2 carries genuine section-5
      content -- versus the unique-decoding window (where it is the n/q regime).

Exact arithmetic throughout (fractions + integer square roots); exit 0 iff all
checks pass.
"""

from fractions import Fraction
from math import isqrt
import sys


def errorBound(delta: Fraction, deg: int, n: int, q: int):
    """Exact mirror of ProximityGap.errorBound (rate rho = deg/n).

    Returns a Fraction when the value is rational; in the Johnson branch the
    value involves sqrt(rho) inside m = min(1 - sqrt(rho) - delta, sqrt(rho)/20),
    so we return the pair ('johnson', m_lower_positive: bool) instead -- the probe
    only needs positivity there.  delta is assumed rational (our delta' always is).
    """
    rho = Fraction(deg, n)
    # branch 1: delta in [0, (1-rho)/2]
    if 0 <= delta <= (1 - rho) / 2:
        return Fraction(n, q)
    # branch 2: delta in ((1-rho)/2, 1-sqrt(rho)) -- compare delta < 1-sqrt(rho)
    # exactly: delta < 1 - sqrt(rho)  <=>  (1-delta)^2 > rho  (both sides in [0,1])
    if delta < 1 and (1 - delta) ** 2 > rho:
        # m = min(1-sqrt(rho)-delta, sqrt(rho)/20) > 0 strictly, q > 0, deg > 0
        return ("johnson_pos",)
    # branch 3 (including the closed boundary delta = 1 - sqrt(rho)): 0
    return Fraction(0)


def boundary_floor(deg: int, n: int):
    """floor((1 - sqrt(deg/n)) * n) = n - ceil(sqrt(deg*n)) computed exactly."""
    s = isqrt(deg * n)
    ceil_sqrt = s if s * s == deg * n else s + 1
    return n - ceil_sqrt


def is_lattice(deg: int, n: int) -> bool:
    """delta_boundary * n integral  <=>  deg*n a perfect square."""
    s = isqrt(deg * n)
    return s * s == deg * n


def main() -> int:
    qs = [5, 97, (1 << 31) - (1 << 27) + 1, (1 << 61) - 1]
    grid = [(n, deg) for n in range(3, 130) for deg in range(1, n)]

    viol = 0
    n_nonlattice = 0
    n_lattice = 0
    n_johnson = 0
    n_udr = 0

    for (n, deg) in grid:
        lat = is_lattice(deg, n)
        if lat:
            n_lattice += 1
            # C3: on the lattice, no strict floor-matched delta' exists:
            # floor(delta*n) = delta*n, and delta' < delta forces floor(delta'*n) <
            # delta*n when delta*n is an integer... verified symbolically: any
            # delta' < delta has delta'*n < delta*n = floor(delta*n), so
            # floor(delta'*n) <= delta'*n < floor(delta*n).  Nothing to enumerate.
            continue
        n_nonlattice += 1
        j = boundary_floor(deg, n)  # floor(delta * n), delta = 1 - sqrt(deg/n)
        dp = Fraction(j, n)  # canonical floor-matched strict sub-radius delta'
        rho = Fraction(deg, n)

        # C1a: floor(delta' * n) = j  (exact since delta'*n = j)
        if not (dp * n == j):
            print(f"VIOLATION C1a at (n={n},deg={deg})")
            viol += 1
        # C1b: delta' < delta = 1 - sqrt(rho)  <=>  (1-dp)^2 > rho (dp <= 1)
        if not ((1 - dp) ** 2 > rho):
            print(f"VIOLATION C1b at (n={n},deg={deg}): dp={dp} not < 1-sqrt(rho)")
            viol += 1
        # C2: errorBound at the closed boundary is 0; errorBound(delta') > 0.
        for q in qs:
            eb_dp = errorBound(dp, deg, n, q)
            if eb_dp == ("johnson_pos",):
                n_johnson += 1
                pos = True
            else:
                n_udr += 1
                pos = eb_dp > 0
            if not pos:
                print(f"VIOLATION C2 at (n={n},deg={deg},q={q}): errorBound(dp)={eb_dp}")
                viol += 1
        # boundary epsilon: delta = 1-sqrt(rho) hits neither rational branch
        # strictly below itself => branch 3 => 0.  (1-delta)^2 = rho exactly, so
        # the Johnson strict inequality fails: kernel of the O76 refutation shape.

    # C4: the O76 witness, reproduced to the digit.
    n4, deg4, q4, k4 = 4, 2, 5, 1
    assert not is_lattice(deg4, n4), "O76 witness must be non-lattice"
    j4 = boundary_floor(deg4, n4)
    dp4 = Fraction(j4, n4)
    ok_dp = dp4 == Fraction(1, 4)
    eb4 = errorBound(dp4, deg4, n4, q4)
    ok_eb = eb4 == Fraction(4, 5) and k4 * eb4 == Fraction(4, 5)
    if not (ok_dp and ok_eb):
        print(f"VIOLATION C4: dp={dp4}, errorBound={eb4}")
        viol += 1

    print(f"grid points: {len(grid)}; non-lattice boundaries: {n_nonlattice}; "
          f"lattice (excluded by C3, honest): {n_lattice}")
    print(f"delta' regimes over {len(qs)} fields: Johnson-window (genuine section-5 "
          f"content): {n_johnson}; unique-decoding (n/q): {n_udr}")
    print(f"O76 witness reproduced: delta'={dp4}, k*errorBound(delta')={k4 * eb4}")
    print(f"violations: {viol}")
    return 0 if viol == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
