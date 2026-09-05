#!/usr/bin/env python3
"""Exact arithmetic audit of the C2 scalar-budget obstruction.

This does not construct polynomial factors or prove a new geometric bound.
The source of the removable rounding is LocatorHybridTransportC2.
exists_firstTail_moving_budgets in official companion commit 032154395c51.
"""

from fractions import Fraction


def add(*flags):
    return tuple(map(sum, zip(*flags)))


def scale(n, flag):
    return tuple(n * x for x in flag)


def mixed(p, q, t):
    z, v, r = p
    a, b, c = q
    x, y, s = t
    return ((c * s + b * s + c * y) * (z + v + r)
            + (a * s + c * x) * (v + r)
            + (b * y + a * y + b * x) * r)


def six_volume(p):
    # Integral of 1 over 0 <= R <= r, R+Y <= r+v,
    # R+Y+Z <= r+v+z, multiplied by 6.
    z, v, r = p
    return (r + v + z) ** 3 - (v + z) ** 3 - 3 * r * z ** 2


def polarized_mixed(p, q, t):
    numerator = (six_volume(add(p, q, t)) - six_volume(add(p, q))
                 - six_volume(add(p, t)) - six_volume(add(q, t))
                 + six_volume(p) + six_volume(q) + six_volume(t))
    assert numerator % 6 == 0
    return numerator // 6


def audit():
    w = 131071
    p = (2317, 37, 10)  # raw coordinates are z, v, r
    z, v, r = p
    normal = (z, v - 1, r - 2)
    centre = (2 * z, 2 * v, 2 * r - 1)
    rational = add(centre, scale(w + 1, normal))
    first_tail = (2 * z * (w + 1), 1 + 2 * v * (w + 1),
                  2 * (r - 1) * (w + 1))
    fiber = (z, v, r + 1)
    cut_published = add(centre, scale(w + 1, p))
    cut_exact = add(centre, scale(w, p))
    unit_flags = ((1, 0, 0), (0, 1, 0), (0, 0, 1))

    # Independent check via polarization of the flag-polytope volume.
    for a in (p, first_tail, rational, fiber, cut_exact, cut_published):
        for b in unit_flags + (p, first_tail, rational):
            for c in unit_flags + (cut_exact, cut_published):
                assert mixed(a, b, c) == polarized_mixed(a, b, c)

    unit_budgets = tuple(mixed(p, first_tail, u) for u in unit_flags)
    main = mixed(p, first_tail, rational)
    assert main == sum(a * b for a, b in zip(rational, unit_budgets))
    moving = mixed(p, fiber, cut_published)
    moving_exact = mixed(p, fiber, cut_exact)
    assert moving - moving_exact == mixed(p, fiber, p)

    published = main + (w + 5) * moving
    tightened = main + (w + 5) * moving_exact
    # Single abstract component with multiplicity 1, saturating each scalar
    # budget. It meets the aggregation inequalities exactly. No geometric
    # realization or local-DVR certificate is asserted.
    atom = main + (w + 1) * moving
    atom_exact = main + (w + 1) * moving_exact
    second_tail = tuple(2 * t * (w + 2) for t in (z, v, r - 1))
    second_tail = (second_tail[0], second_tail[1] + 1, second_tail[2])
    padded = mixed(p, first_tail, second_tail)
    assert atom <= padded
    assert atom_exact <= padded
    assert 100 * atom_exact > 94 * published

    fixed_other = 8728752287324751 + 73789382345390 + 5529601254
    field = 274980728111395087
    assert published == 283403712362442072
    assert published + fixed_other == 292206259561713467

    # Conditional geometric calculation only: if the U=0,Q=t base locus
    # consists of the full expected transverse intersection, subtracting k
    # per base point would give this value. The properness hypotheses and
    # global subtraction theorem have NOT been established.
    conditional_base_correction = (w + 5) * w * mixed(
        p, unit_flags[1], scale(2, unit_flags[2]))

    values = {
        "raw_flag_z_v_r": p,
        "unit_budgets_z_yz_all": unit_budgets,
        "main": main,
        "moving_budget_published": moving,
        "moving_budget_exact": moving_exact,
        "moving_contribution": (w + 5) * moving,
        "published_singleton": published,
        "tightened_singleton": tightened,
        "rigorous_rounding_saving": published - tightened,
        "rigorous_rounding_saving_percent": float(Fraction(
            100 * (published - tightened), published)),
        "abstract_mu_one_atom": atom,
        "abstract_mu_one_atom_with_exact_cut": atom_exact,
        "abstract_atom_remaining_excess_with_same_complement":
            atom_exact + fixed_other - field,
        "padded_alternative": padded,
        "conditional_base_locus_saving": conditional_base_correction,
    }
    for key, value in values.items():
        print(f"{key}: {value}")
    print("PASS: exact arithmetic; abstract budget obstruction only")


if __name__ == "__main__":
    audit()
