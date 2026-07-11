#!/usr/bin/env python3
"""Probe: the CORRECTED boundary threshold statement (O76) at 4 parameter points,
plus the floor-cell threshold-monotonicity brick it needs.

Issue #304 / #232.  O76 refuted BOTH nonemptiness leaves of the boundary
quantization split and recorded the corrected obligation: at a non-lattice
Johnson endpoint delta = 1 - sqrt(rho), the boundary export must carry the
section-5 probability threshold at a floor-matched STRICT radius delta' < delta:

    Pr[good at delta'] > k * errorBound(delta')  ==>  jointAgreement at delta'.

This probe does two things.

(a) VIOLATION HUNT, 4 points (vary k, deg, n, q incl. a large q), all with
    deg*n NON-square (genuinely non-lattice endpoints):
      P1: q=5,   n=4, deg=2, k=1  -- EXHAUSTIVE over all q^(2n) stacks
      P2: q=13,  n=6, deg=2, k=1  -- sampled (random + 3 adversarial families)
      P3: q=257, n=6, deg=2, k=1  -- larger q, sampled
      P4: q=13,  n=4, deg=2, k=2  -- wider stack, sampled
    KEY REDUCTION (this is the monotonicity insight being shipped to Lean):
    the good set and jointAgreement depend on delta' only through the floor
    j = floor(delta*n), which is CONSTANT over floor-matched delta'; and
    errorBound is monotone nondecreasing on [0, 1-sqrt(rho)) (in-tree
    DivergenceOfSets.errorBound_mono).  Hence the corrected statement is
    violated at SOME floor-matched delta' iff it is violated at the cell's
    left endpoint delta'_min = j/n, where errorBound is smallest.  So the
    hunt tests exactly:  #good(j)/q > k*errorBound(j/n)  and  not JA(j).

(b) MONOTONICITY GRID: errorBound nondecreasing across a delta grid in
    [0, 1-sqrt(rho)) at each point, including cross-branch (UDR -> Johnson)
    pairs; plus the deg = 0 NEGATIVE CONTROL showing monotonicity FAILS
    without 0 < deg (the in-tree hdeg hypothesis is load-bearing).

Exit 0 iff: no violation of the corrected statement found, monotonicity grid
clean, and the deg=0 control fails as expected.
"""

import itertools
import math
import random

random.seed(232078)

VIOLATIONS = []


def inv_mod(a, q):
    return pow(a, q - 2, q)


def make_code_params(q, n, deg):
    """RS code = evals of polys of degree < deg on domain {0..n-1} in GF(q)."""
    assert deg == 2, "probe specialised to deg=2 (linear codewords)"
    domain = list(range(n))
    return domain


def line_eval(a, b, x, q):
    return (a + b * x) % q


def max_agreement_deg2(w, domain, q):
    """Max #coords where w agrees with some a+bx; exact whenever >= 2."""
    n = len(domain)
    best = 1
    for i in range(n):
        for jj in range(i + 1, n):
            xi, xj = domain[i], domain[jj]
            b = ((w[jj] - w[i]) * inv_mod(xj - xi, q)) % q
            a = (w[i] - b * xi) % q
            agree = sum(1 for t in range(n) if line_eval(a, b, domain[t], q) == w[t])
            if agree > best:
                best = agree
    return best


def dist_from_code(w, domain, q):
    return len(domain) - max_agreement_deg2(w, domain, q)


def word_has_agreeing_codeword_on(w, S, domain, q):
    """Does some a+bx match w on ALL of S (|S| >= 2)?"""
    i, jj = S[0], S[1]
    xi, xj = domain[i], domain[jj]
    b = ((w[jj] - w[i]) * inv_mod(xj - xi, q)) % q
    a = (w[i] - b * xi) % q
    return all(line_eval(a, b, domain[t], q) == w[t] for t in S)


def joint_agreement(stack, j, domain, q):
    """Exists S, |S| >= n - j, with per-word agreeing codewords on S."""
    n = len(domain)
    need = n - j
    assert need >= 2
    for S in itertools.combinations(range(n), need):
        if all(word_has_agreeing_codeword_on(w, S, domain, q) for w in stack):
            return True
    return False


def error_bound(dp, n, deg, q):
    """In-tree ProximityGap.errorBound at radius dp (rho = deg/n)."""
    rho = deg / n
    if dp <= (1 - rho) / 2 + 1e-15:
        return n / q
    if (1 - rho) / 2 < dp < 1 - math.sqrt(rho):
        m = min(1 - math.sqrt(rho) - dp, math.sqrt(rho) / 20)
        if m <= 0:
            return 0.0
        return deg ** 2 / ((2 * m) ** 7 * q)
    return 0.0


def good_count(stack, j, domain, q, k):
    g = 0
    n = len(domain)
    for z in range(q):
        w = tuple(sum(stack[t][i] * pow(z, t, q) for t in range(k + 1)) % q
                  for i in range(n))
        if dist_from_code(w, domain, q) <= j:
            g += 1
    return g


def check_stack(stack, point, j, dpmin_thr, domain, q, k, stats):
    g = good_count(stack, j, domain, q, k)
    stats["max_g"] = max(stats["max_g"], g)
    fires = g / q > dpmin_thr
    if fires:
        stats["fired"] += 1
        ja = joint_agreement(stack, j, domain, q)
        if not ja:
            VIOLATIONS.append((point, stack, g))
            return
    else:
        # census: track max good count among NO-jointAgreement stacks
        if g > stats["max_g_noja"]:
            if not joint_agreement(stack, j, domain, q):
                stats["max_g_noja"] = g


def random_codeword(domain, q):
    a, b = random.randrange(q), random.randrange(q)
    return [line_eval(a, b, x, q) for x in domain]


def planted_stacks(domain, q, k, j, count):
    """Adversarial families: (A) shared-support cancellation, (B) multi-z
    codeword bundles, (C) low-weight direction (control: JA should hold)."""
    n = len(domain)
    out = []
    for _ in range(count // 3):
        # (A) u_t = c_t + e_t, errors on shared support T of size j+1
        T = random.sample(range(n), j + 1)
        stack = []
        for _t in range(k + 1):
            c = random_codeword(domain, q)
            for i in T:
                c[i] = (c[i] + random.randrange(1, q)) % q
            stack.append(tuple(c))
        out.append(tuple(stack))
    for _ in range(count // 3):
        # (B) two planted close z's: solve u0 + z1*u1 = w1+e1, u0 + z2*u1 = w2+e2
        # (k=1 exact; for k>1 set higher words to small perturbations of codewords)
        z1, z2 = random.sample(range(q), 2)
        w1, w2 = random_codeword(domain, q), random_codeword(domain, q)
        e1 = [0] * n
        e2 = [0] * n
        for i in random.sample(range(n), j):
            e1[i] = random.randrange(q)
        for i in random.sample(range(n), j):
            e2[i] = random.randrange(q)
        v1 = [(w1[i] + e1[i]) % q for i in range(n)]
        v2 = [(w2[i] + e2[i]) % q for i in range(n)]
        inv = inv_mod(z2 - z1, q)
        u1 = tuple((v2[i] - v1[i]) * inv % q for i in range(n))
        u0 = tuple((v1[i] - z1 * u1[i]) % q for i in range(n))
        stack = [u0, u1]
        for _t in range(k - 1):
            c = random_codeword(domain, q)
            i = random.randrange(n)
            c[i] = (c[i] + random.randrange(1, q)) % q
            stack.append(tuple(c))
        out.append(tuple(stack))
    while len(out) < count:
        # (C) low-weight direction over a codeword base: every z is good
        c = tuple(random_codeword(domain, q))
        stack = [c]
        for _t in range(k):
            e = [0] * n
            for i in random.sample(range(n), j):
                e[i] = random.randrange(1, q)
            stack.append(tuple(e))
        out.append(tuple(stack))
    return out


def run_point(name, q, n, deg, k, exhaustive, samples=6000):
    domain = make_code_params(q, n, deg)
    rho = deg / n
    assert int(math.isqrt(deg * n)) ** 2 != deg * n, "endpoint must be non-lattice"
    delta = 1 - math.sqrt(rho)
    j = math.floor(delta * n)
    dpmin = j / n
    assert math.floor(dpmin * n) == j and dpmin < delta
    eb = error_bound(dpmin, n, deg, q)
    thr = k * eb
    branch = "UDR" if dpmin <= (1 - rho) / 2 + 1e-15 else "Johnson"
    print(f"\n== {name}: q={q} n={n} deg={deg} k={k}  delta={delta:.4f} j={j} "
          f"delta'_min={dpmin:.4f} [{branch}]  k*errorBound={thr:.4f} "
          f"(need #good > {thr * q:.2f})")
    stats = {"max_g": 0, "fired": 0, "max_g_noja": 0, "n_stacks": 0}
    if exhaustive:
        words = list(itertools.product(range(q), repeat=n))
        total = 0
        for u0 in words:
            for u1 in words:
                check_stack((u0, u1), name, j, thr, domain, q, k, stats)
                total += 1
        stats["n_stacks"] = total
    else:
        stacks = []
        for _ in range(samples // 2):
            stacks.append(tuple(tuple(random.randrange(q) for _ in range(n))
                                for _t in range(k + 1)))
        stacks += planted_stacks(domain, q, k, j, samples - len(stacks))
        for s in stacks:
            check_stack(s, name, j, thr, domain, q, k, stats)
        stats["n_stacks"] = len(stacks)
    print(f"   stacks={stats['n_stacks']}  threshold fired on {stats['fired']}  "
          f"max #good={stats['max_g']}  max #good among no-JA={stats['max_g_noja']}  "
          f"violations so far={len(VIOLATIONS)}")
    return stats


def monotonicity_grid(q, n, deg, steps=400):
    """errorBound nondecreasing on [0, 1-sqrt(rho)); count cross-branch pairs."""
    rho = deg / n
    hi = 1 - math.sqrt(rho)
    grid = [hi * t / steps for t in range(steps)]  # strictly below hi
    bad = 0
    cross = 0
    prev = -1.0
    prev_d = 0.0
    for d in grid:
        e = error_bound(d, n, deg, q)
        if e < prev - 1e-12:
            bad += 1
            print(f"   MONOTONICITY VIOLATION q={q} n={n} deg={deg}: "
                  f"eb({prev_d:.4f})={prev:.4g} > eb({d:.4f})={e:.4g}")
        if prev_d <= (1 - rho) / 2 + 1e-15 < d:
            cross += 1
        prev, prev_d = e, d
    return bad, cross


def main():
    # ---- (a) violation hunt, 4 points ----
    run_point("P1-exhaustive", q=5, n=4, deg=2, k=1, exhaustive=True)
    run_point("P2", q=13, n=6, deg=2, k=1, exhaustive=False)
    run_point("P3-largeq", q=257, n=6, deg=2, k=1, exhaustive=False, samples=4000)
    run_point("P4-k2", q=13, n=4, deg=2, k=2, exhaustive=False)

    assert not VIOLATIONS, f"CORRECTED STATEMENT VIOLATED: {VIOLATIONS[:3]}"
    print("\n(a) corrected threshold statement: NO violation at any point")

    # ---- (b) monotonicity grid (the Lean brick's numeric shadow) ----
    total_bad = 0
    total_cross = 0
    for (q, n, deg) in [(5, 4, 2), (13, 6, 2), (257, 6, 2), (101, 8, 3)]:
        bad, cross = monotonicity_grid(q, n, deg)
        total_bad += bad
        total_cross += cross
    print(f"(b) errorBound monotone on [0,1-sqrt(rho)) across 4 grids: "
          f"violations={total_bad}, cross-branch seams checked={total_cross}")
    assert total_bad == 0

    # deg = 0 negative control: monotonicity FAILS without 0 < deg
    # (rho=0: errorBound = n/q on [0,1/2], but 0 on (1/2,1) since m=0 kills
    # the Johnson value).  This shows hdeg in errorBound_mono is load-bearing.
    n, q = 6, 13
    lo = error_bound(0.4, n, 0, q)
    hi = error_bound(0.6, n, 0, q)
    print(f"(b-control) deg=0: eb(0.4)={lo:.4f} > eb(0.6)={hi:.4f} "
          f"-- monotonicity fails without 0<deg, as the in-tree hdeg demands")
    assert lo > hi, "deg=0 control unexpectedly monotone"

    # floor-cell transport restated (what the Lean brick proves): within the
    # cell [j/n, delta), Pr is constant and the threshold k*eb is monotone, so
    # threshold at any floor-matched delta' implies it at all smaller ones.
    for (q, n, deg) in [(5, 4, 2), (13, 6, 2), (257, 6, 2)]:
        rho = deg / n
        delta = 1 - math.sqrt(rho)
        j = math.floor(delta * n)
        cell = [j / n + (delta - j / n) * t / 50 for t in range(50)]
        ebs = [error_bound(d, n, deg, q) for d in cell]
        assert all(ebs[i] <= ebs[i + 1] + 1e-12 for i in range(len(ebs) - 1)), \
            f"floor-cell monotonicity broken at q={q}"
    print("(b) floor-cell transport: threshold descends within every cell "
          "checked (3 cells x 50 radii)")

    print("\nPROBE VERDICT: corrected boundary threshold statement SURVIVES "
          "(P1 exhaustive + P2/P3/P4 sampled, incl. q=257 and k=2); errorBound "
          "floor-cell monotonicity confirmed; deg=0 control confirms hdeg is "
          "load-bearing.")


if __name__ == "__main__":
    main()
