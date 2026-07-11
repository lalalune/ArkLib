#!/usr/bin/env python3
"""
DECISIVE set-level probe for EvenDirectionIncidenceCollapse (issue #407,
Frontier/EvenDirectionDescent.lean).

The 2-adic even-odd descent claims the even/imprimitive monomial direction x^{2a'} on mu_n
(against RS[mu_n, 2k]) has the SAME far-line incidence SET as the descended direction x^{a'}
on mu_{n/2} (against RS[mu_{n/2}, k]).  The squaring map f: mu_n -> mu_{n/2}, x|->x^2 is 2-to-1.

Lean PROVEN forward leg (explainableScalars_sq_pullback_subset):
    bad_{n/2}(x^{a'}; r')   SUBSET   bad_n(x^{2a'}; 2r')          [half injects into full]
Lean OPEN reverse leg (EvenDirectionIncidenceCollapse):
    bad_n(x^{2a'}; 2r')     SUBSET   bad_{n/2}(x^{a'}; r')        [the collapse]

RADIUS TRANSPORT: witness S' of size m'=(n/2)-r' on mu_{n/2} pulls back under f to size 2m' on
mu_n, so the matched full radius is r = 2 r' (size_f = n - 2r' = 2 size_h).

This script computes BOTH bad-SETS exactly (the Lean Prop is set containment) and reports
whether reverse (collapse) holds.  RESULT (2026-06-14, p-independent across 3 primes):
  n=8  k=2: collapse HOLDS on every cell.
  n=16 k=4: collapse FAILS at exactly ONE cell — the deepest 2-adic direction x^8 (= +-1 on
            mu_16, lands in mu_2) at binding radius r'=3:  I_half=20, I_full=36, excess=16,
            full\\half = 16 "odd-part" bad gammas that do NOT descend (half SUBSET full holds).
  => the even half of the 2-adic tower is NOT closed; the deepest sign-direction x^{n/2}
     genuinely amplifies, exactly the odd-part mechanism the Lean docstring names.
"""
import sys, itertools, math
sys.path.insert(0, '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from prize_workspace import subgroup
from probe_farline_incidence_exact import find_prime_cong1, left_null


def incidence_set(S, p, k, a, b, r):
    """(frozenset_of_bad_gammas, saturated_bool).  saturated => all of F_p."""
    n = len(S); size = n - r
    if size <= k:
        return None, True
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P:
            continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return None, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good.add(g)
    return frozenset(good), False


def census(n, k, p=None):
    """Return (p, cells, fails); fails = reverse-collapse failures w/ 2-adic direction depth."""
    nh = n // 2
    if p is None:
        p = find_prime_cong1(n, 200003)
    Sf = subgroup(p, n); Sh = subgroup(p, nh)
    cells = []; fails = []
    for rprime in range(0, nh - k):
        size_h = nh - rprime
        if size_h <= k:
            continue
        r_full = 2 * rprime; size_f = n - r_full
        if size_f <= 2 * k:
            continue
        for aprime in range(k, size_h):       # far direction x^{a'} on mu_{n/2}
            for a0 in range(nh):
                if a0 == aprime:
                    continue
                sh, sah = incidence_set(Sh, p, k, a0, aprime, rprime)
                sf, saf = incidence_set(Sf, p, 2 * k, 2 * a0, 2 * aprime, r_full)
                ch = p if sah else len(sh); cf = p if saf else len(sf)
                # forward (proven): half subset full
                if sah:
                    fwd = saf
                elif saf:
                    fwd = True
                else:
                    fwd = sh <= sf
                # reverse (open collapse): full subset half
                if saf:
                    rev = sah
                elif sah:
                    rev = True
                else:
                    rev = sf <= sh
                cells.append((a0, aprime, rprime, ch, cf, fwd, rev))
                if not rev:
                    g = math.gcd(n, 2 * aprime); lvl = n // g  # x^{2a'} lands in mu_lvl
                    fails.append((a0, aprime, 2 * aprime, rprime, ch, cf, cf - ch, lvl, fwd, rev))
    return p, cells, fails


if __name__ == '__main__':
    print("=== EvenDirectionIncidenceCollapse audit: bad_n(x^{2a'}) vs bad_{n/2}(x^{a'}) ===")
    print("forward(proven): half SUBSET full ;  reverse(OPEN collapse): full SUBSET half\n")
    for (n, k) in [(8, 2), (16, 4), (16, 2)]:
        p, cells, fails = census(n, k)
        fwd_fail = [c for c in cells if not c[5]]
        print(f"n={n} k={k} (rho={k}/{n}) p={p}: {len(cells)} cells, "
              f"forward-fails={len(fwd_fail)}, reverse(collapse)-fails={len(fails)}")
        if not fails:
            print("  COLLAPSE HOLDS on every cell (even tower closed at this size).")
        else:
            from collections import Counter
            lc = Counter(f[7] for f in fails)
            print(f"  COLLAPSE FAILS. amplification cells by direction depth (mu_lvl): {dict(lc)}")
            for f in sorted(fails, key=lambda f: -f[6])[:6]:
                a0, ap, d, rp, ch, cf, exc, lvl, fwd, rev = f
                print(f"    a0={a0} a*={ap} dir=x^{d}(mu_{lvl}) r*={rp}: "
                      f"I_half={ch} I_full={cf} excess={exc} fwd_ok={fwd} rev_ok={rev}")
        print()
    print("cross-prime stability of n=16 k=4 binding cell (a0=6,a*=4,dir x^8,r*=3):")
    for pl in (200003, 500003, 1000003):
        p = find_prime_cong1(16, pl)
        Sf = subgroup(p, 16); Sh = subgroup(p, 8)
        sh, _ = incidence_set(Sh, p, 4, 6, 4, 3)
        sf, _ = incidence_set(Sf, p, 8, 12, 8, 6)
        print(f"  p={p}: I_half={len(sh)} I_full={len(sf)} excess={len(sf)-len(sh)} "
              f"half_sub_full={sh<=sf} full_sub_half={sf<=sh} |full\\half|={len(sf-sh)}")
