#!/usr/bin/env python3
"""
probe_407_badcollapse_thinness.py  (#444 / #407 census->CORE lane)

THE UNPROBED QUESTION (flagged by the census<->CORE map, DISPROOF_LOG c.1037 +
probe_407_census_core_bindingband_ratio.py): that map showed at the hifreq BINDING line
#bad COLLAPSES to O(1) while #alignable overcounts up to 112x; it concluded "CORE-effort
should target #bad directly -- the #bad collapse to O(1) at the hifreq line is the real
CORE signal." But NO probe has tested whether the #bad collapse ITSELF is THINNESS-ESSENTIAL.

#bad = number of distinct gamma s.t. the far line x^A + gamma*x^B agrees with a deg<k RS
codeword on a size-a subset of the subgroup G (a = binding band = the deepest a with supply).
This is exactly the in-tree CORE/epsMCA object (epsMCA <= #bad/p).

RULE-3 TEST: is "#bad = O(1) at the hifreq binding line" a 2-power(THIN)-essential phenomenon,
or thickness-monotone? If #bad stays O(1) for THIN n=2^a but BLOWS UP for THICK subgroups of
comparable order at the SAME hifreq line, that is a genuine thin-essential CORE signal (rule-3
PASS -> a live lever). If #bad is O(1) in BOTH regimes, the collapse is thickness-monotone
(rule-3 FAIL) -> another mapped wall, and the "target #bad" recommendation inherits the
far-line-incidence-is-just-Johnson fate.

METHOD: exact mod-p. Proper subgroup G = <g>, |G| = n, index m = (p-1)/n >= 2, NEVER n = q-1.
Compare:
  THIN  : n = 2^a  (8, 16, 32) -- the prize family.
  THICK : n with small odd part removed-vs-present; use n = 12, 18, 20, 24, 36 (thick beta,
          where the prize is FALSE) at matched k, hifreq line.
For each: scan band a downward from n-1, find the binding band (deepest a with #align>0),
report #bad there AND the #bad profile across the (halfJ, J) window. Multi-prime for
p-invariance. k=3 (the deep-ceiling m=2 shape the weld binds at).

NO Lean change => axiom-clean trivially.
"""
import itertools
from math import comb, isqrt

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True

def prime_1modn(target, n):
    p = target + (1 - target) % n
    if p < 2: p += n
    while not (isprime(p) and (p-1) % n == 0): p += n
    return p

def _pf(n):
    f = set(); d = 2; m = n
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f

def find_g(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in _pf(n)):
            return x
    raise ValueError(f"no generator for order {n} mod {p}")

def dd_cached(idxs, u, invdiff, p):
    """divided-difference leading coeff via PRECOMPUTED inverse pairwise diffs (no modpow in loop).
    invdiff[i][j] = (xs[i]-xs[j])^{-1} mod p."""
    t = 0
    for i in idxs:
        w = 1
        row = invdiff[i]
        for j in idxs:
            if i != j:
                w = w * row[j] % p
        t = (t + u[i] * w) % p
    return t

def badset_band(n, p, g, A, B, k, a, _cache={}):
    """Return (#align a-sets, set of distinct bad gammas) for far line x^A + g*x^B vs RS[deg<k => k+1 nodes].
    Caches xs/u0/u1/invdiff per (p,g,A,B,n)."""
    key = (p, g, A, B, n)
    if key not in _cache:
        xs = [pow(g, i, p) for i in range(n)]
        u0 = [pow(x, A, p) for x in xs]
        u1 = [pow(x, B, p) for x in xs]
        invdiff = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i != j:
                    invdiff[i][j] = pow((xs[i]-xs[j]) % p, p-2, p)
        _cache.clear()  # keep memory bounded: one line at a time
        _cache[key] = (u0, u1, invdiff)
    u0, u1, invdiff = _cache[key]
    align = 0
    bad = set()
    for S in itertools.combinations(range(n), a):
        gam = None; ok = True; nd = False
        for T in itertools.combinations(S, k+1):
            e1 = dd_cached(T, u1, invdiff, p)
            e0 = dd_cached(T, u0, invdiff, p)
            if e1 == 0:
                if e0 != 0: ok = False; break
                continue
            nd = True
            gT = (-e0 * pow(e1, p-2, p)) % p
            if gam is None: gam = gT
            elif gam != gT: ok = False; break
        if ok and nd and gam is not None:
            align += 1
            bad.add(gam)
    return align, bad

def scan_line(n, p, g, A, B, k, max_combo=6_000_000):
    """Scan band a from n-1 downward over DEEP bands only (comb(n,a) feasible).
    The binding band is the deepest a with supply; deep bands have small comb(n,a).
    We stop once comb(n,a) exceeds max_combo (mid-range bands are not the binding object
    and are combinatorially infeasible at n=32). Return list of (a,#align,#bad), ascending a."""
    rows = []
    for a in range(n-1, k, -1):
        if comb(n, a) > max_combo:
            break  # too deep into the mid-band; binding (deepest) already captured if present
        al, bs = badset_band(n, p, g, A, B, k, a)
        if al > 0:
            rows.append((a, al, len(bs)))
    rows.sort()  # ascending a
    return rows

def report(label, n, primes, k, lines):
    print(f"\n## {label}: n={n} k={k} (THIN=2-power)  primes={primes}")
    for (A, B, nm) in lines:
        print(f"  line {nm} [{A},{B}]:", flush=True)
        for p in primes:
            try:
                g = find_g(p, n)
            except ValueError:
                print(f"    p={p}: no order-{n} subgroup, skip"); continue
            rows = scan_line(n, p, g, A, B, k)
            if not rows:
                print(f"    p={p}: no supply"); continue
            # binding band = deepest a (largest), i.e. last in ascending list
            a_b, al_b, bd_b = rows[-1]
            johnson_s = k + isqrt(k*n)  # approx agreement size at Johnson
            prof = " ".join(f"a{a}:{bd}" for (a, al, bd) in rows)
            print(f"    p={p}: BINDING a={a_b} #bad={bd_b} (#align={al_b})  | #bad-profile: {prof}  | Johnson-s~{johnson_s}", flush=True)

def main():
    print("# probe_407_badcollapse_thinness: is the #bad-collapse-to-O(1) at the hifreq binding line THINNESS-ESSENTIAL?")
    print("# #bad = distinct gamma s.t. far line x^A+g*x^B agrees with deg<k codeword on size-a subgroup subset.")
    print("# RULE-3: O(1) only for THIN(2-power)? -> live lever. O(1) in BOTH thin+thick? -> thickness-monotone wall.")
    print("# proper subgroup, index m=(p-1)/n>=2, NEVER n=q-1.")

    k = 3
    # hifreq lines (the binding family): high exponents, the [9,7]/[7,6] family from the census map.
    # ---- THIN 2-power family ----
    report("THIN 2^3", 8, [prime_1modn(7937, 8), prime_1modn(40009, 8)], k,
           [(5,4,"hifreq"), (6,5,"hifreq2"), (3,2,"KKH")])
    report("THIN 2^4", 16, [prime_1modn(65537, 16), prime_1modn(160001, 16)], k,
           [(9,7,"hifreq"), (7,6,"hifreq2"), (6,4,"KKH")])
    # n=32: deep bands only (comb cap keeps it feasible; binding for hifreq is deep => small comb)
    report("THIN 2^5", 32, [prime_1modn(1048609, 32)], k,
           [(18,16,"hifreq"), (15,13,"hifreq2")])

    # ---- THICK family (prize is FALSE here; n with large odd part / smaller beta) ----
    report("THICK n=12", 12, [prime_1modn(20749, 12), prime_1modn(100003, 12)], k,
           [(7,5,"hifreq"), (5,4,"hifreq2"), (4,2,"KKH")])
    report("THICK n=18", 18, [prime_1modn(100003, 18)], k,
           [(10,8,"hifreq"), (8,7,"hifreq2"), (6,3,"KKH")])
    report("THICK n=20", 20, [prime_1modn(100003, 20)], k,
           [(11,9,"hifreq"), (9,8,"hifreq2"), (7,4,"KKH")])

    print("\n# VERDICT (read the #bad at BINDING a, thin vs thick): ")
    print("#   if THIN #bad=O(1) and THICK #bad>>1 at binding -> THINNESS-ESSENTIAL collapse (rule-3 PASS, live lever)")
    print("#   if BOTH O(1) -> thickness-monotone (rule-3 FAIL, mapped wall)")

if __name__ == '__main__':
    main()
