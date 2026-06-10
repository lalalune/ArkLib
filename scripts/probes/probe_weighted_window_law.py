#!/usr/bin/env python3
"""Probe (O108 candidate): the WEIGHTED windowed two-prime law.

Conjecture: for n = p^a*q^b, zeta a primitive n-th root of unity (char 0),
w : [0,n) -> N, and window length t < n:

    (forall j, 1 <= j <= t -> sum_e w_e zeta^{j e} = 0)
        <=>  w is an N-combination of indicator vectors of canonical rotated
             mu_d-cosets with d | n, d > t
        (equivalently: exists A_d : [0, n/d) -> N with
         w_e = sum_{d | n, d > t} A_d(e % (n/d))).

The 0/1 case is O106 (windowed_two_prime); the t = 1 case is O103
(debruijn_weighted_two_prime).  This probe tests the general-multiplicity,
general-t statement EXHAUSTIVELY on a coefficient box, plus the converse on
random combinations.

Method: exact integer arithmetic in Z[x]/Phi_n.  For each w in {0..B}^n we
compute the maximal initial window t*(w) (largest t with all 1 <= j <= t sums
vanishing; vanishing checked by reducing sum_e w_e x^{(j e) % n} mod Phi_n
over Z).  Then we check that w decomposes as an N-combination of mu_d-coset
indicators with d > t*(w) (decomposability for smaller t is implied since the
generator set only grows).  Branching is finite: a coset through position e at
divisor d is unique (base e % (n/d)), so the backtracking decomposer branches
over divisors only.

Exit 0 iff every box point decomposes at its own t* and all converse samples
vanish on their windows.
"""

import sys
import itertools
import random
from functools import lru_cache


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def cyclotomic(n, cache={}):
    """Phi_n over Z as a list of coefficients (low to high), via recursive
    exact division of x^n - 1 by prod of Phi_d, d | n, d < n."""
    if n in cache:
        return cache[n]
    poly = [-1] + [0] * (n - 1) + [1]  # x^n - 1
    for d in divisors(n)[:-1]:
        phi_d = cyclotomic(d)
        poly = polydiv_exact(poly, phi_d)
    cache[n] = poly
    return poly


def polydiv_exact(num, den):
    """Exact division of integer polynomials (den monic)."""
    num = num[:]
    dn, dd = len(num) - 1, len(den) - 1
    out = [0] * (dn - dd + 1)
    for k in range(dn - dd, -1, -1):
        c = num[dd + k]
        out[k] = c
        if c:
            for i, dc in enumerate(den):
                num[i + k] -= dc * c
    assert all(c == 0 for c in num[:dd]) and all(c == 0 for c in num[dd:dd + 1] if False), "non-exact division"
    return out


def reduce_mod_phi(vec_n, phi):
    """Reduce a length-n coefficient vector mod Phi_n (monic), exact ints."""
    poly = vec_n[:]
    dd = len(phi) - 1
    for k in range(len(poly) - 1, dd - 1, -1):
        c = poly[k]
        if c:
            for i, dc in enumerate(phi):
                poly[i + k - dd] -= dc * c
    return poly[:dd]


def power_residues(n, phi):
    """R[e] = x^e mod Phi_n as a tuple, for e in [0, n)."""
    out = []
    for e in range(n):
        vec = [0] * n
        vec[e] = 1
        out.append(tuple(reduce_mod_phi(vec, phi)))
    return out


def window_star(w, n, R, deg):
    """Largest t such that sum_e w_e zeta^{j e} = 0 for all 1 <= j <= t."""
    t = 0
    for j in range(1, n):
        acc = [0] * deg
        for e, we in enumerate(w):
            if we:
                r = R[(j * e) % n]
                for i in range(deg):
                    acc[i] += we * r[i]
        if any(acc):
            break
        t = j
    return t


def gens_for(n, t):
    """Coset generators (d, base) -> support tuple, for d | n, d > t, d < n+1."""
    out = {}
    for d in divisors(n):
        if d > t:
            step = n // d
            for r in range(step):
                out[(d, r)] = tuple(r + s * step for s in range(d))
    return out


def decomposes(w, n, t):
    """Backtracking: can w be written as an N-combination of mu_d-coset
    indicators with d | n, d > t?  Branch over divisors at the first nonzero
    position (the coset through a position at a given d is unique)."""
    ds = [d for d in divisors(n) if d > t]
    steps = {d: n // d for d in ds}

    @lru_cache(maxsize=None)
    def go(wt):
        try:
            e0 = next(e for e, we in enumerate(wt) if we)
        except StopIteration:
            return True
        for d in ds:
            step = steps[d]
            base = e0 % step
            support = [base + s * step for s in range(d)]
            if all(wt[e] >= 1 for e in support):
                nxt = list(wt)
                for e in support:
                    nxt[e] -= 1
                if go(tuple(nxt)):
                    return True
        return False

    return go(tuple(w))


def run_box(n, B):
    phi = cyclotomic(n)
    deg = len(phi) - 1
    R = power_residues(n, phi)
    checked = vanishing = 0
    failures = []
    for w in itertools.product(range(B + 1), repeat=n):
        checked += 1
        if not any(w):
            continue
        ts = window_star(w, n, R, deg)
        if ts == 0:
            continue
        vanishing += 1
        if not decomposes(w, n, ts):
            failures.append((w, ts))
            if len(failures) > 5:
                break
    return checked, vanishing, failures


def run_converse(n, trials, seed=232):
    """Random N-combinations of d > t cosets must vanish on the window."""
    rng = random.Random(seed)
    phi = cyclotomic(n)
    deg = len(phi) - 1
    R = power_residues(n, phi)
    bad = []
    for _ in range(trials):
        t = rng.randrange(1, n)
        gens = list(gens_for(n, t).values())
        if not gens:
            continue
        w = [0] * n
        for _ in range(rng.randrange(1, 5)):
            g = rng.choice(gens)
            c = rng.randrange(1, 4)
            for e in g:
                w[e] += c
        ts = window_star(w, n, R, deg)
        if ts < t and any(w):
            bad.append((n, t, ts, tuple(w)))
    return bad


def main():
    ok = True
    # exhaustive boxes (n, B): full multiplicity boxes at two-prime n
    for n, B in [(12, 2), (18, 1), (12, 3)]:
        if (n, B) == (12, 3):
            # sampled corner: full 4^12 is ~17M; sample the box instead
            phi = cyclotomic(n)
            deg = len(phi) - 1
            R = power_residues(n, phi)
            rng = random.Random(108)
            failures = []
            vanishing = 0
            for _ in range(400000):
                w = tuple(rng.randrange(B + 1) for _ in range(n))
                if not any(w):
                    continue
                ts = window_star(w, n, R, deg)
                if ts == 0:
                    continue
                vanishing += 1
                if not decomposes(w, n, ts):
                    failures.append((w, ts))
                    if len(failures) > 5:
                        break
            print(f"n={n} B={B} (sampled 400k): vanishing={vanishing} failures={len(failures)}")
            if failures:
                ok = False
                for w, ts in failures[:3]:
                    print("  FAIL:", w, "t*=", ts)
            continue
        checked, vanishing, failures = run_box(n, B)
        print(f"n={n} B={B}: checked={checked} vanishing={vanishing} failures={len(failures)}")
        if failures:
            ok = False
            for w, ts in failures[:3]:
                print("  FAIL:", w, "t*=", ts)
    # converse samples
    for n in (12, 18, 20):
        bad = run_converse(n, 2000)
        print(f"n={n} converse trials=2000 bad={len(bad)}")
        if bad:
            ok = False
            for rec in bad[:3]:
                print("  BAD:", rec)
    print("PROBE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
