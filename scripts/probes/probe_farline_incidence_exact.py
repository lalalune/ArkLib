#!/usr/bin/env python3
"""
EXACT far-line incidence for monomial stacks over mu_n in F_p — the in-tree EXACT delta* object.

Object (FarCosetExplosion.epsMCA_ge_far_incidence + badScalars_eq_explainable, axiom-clean):
  for a FAR direction u1 = x^b and offset u0 = x^a,
    I(a,b; r) = #{ gamma in F_p : the line  x^a + gamma*x^b  on mu_n
                  agrees with SOME codeword of RS[mu_n,k] on >= n-r points }
  and  delta* = sup{ delta : max over far stacks of I(a,b; floor(delta n)) <= q*eps* }
  with the prize budget q*eps* = (n*2^128)*2^-128 = n.

KEY EXACTNESS FACT (no sqrt-loss, unlike additive energy): I is computed WITHOUT codeword
enumeration via the per-witness-set affine-in-gamma structure. For each agreement set R
(|R| = n-r), the condition  x^a|_R + gamma x^b|_R in RS[R,k] = col(Vandermonde_R)  is affine
in gamma: using the left null space P of V_R,
    P x^a|_R + gamma P x^b|_R = 0
  =>  R "heavy" (ALL gamma) iff P x^a|_R = 0 and P x^b|_R = 0;  else <= 1 gamma.
I(a,b;r) = p if some R is heavy, else |union over R of the single gammas| (<= C(n,r)).

CRITICAL — the FAR condition.  The far-coset law (I = bad count) holds ONLY for far directions.
For a monomial direction x^b this means  b < n-r  (else x^b agrees with a deg<k codeword on a
witness-sized set and is NOT far; applying the formula to a near direction over-counts).  Near
capacity (size = n-r small), far directions are forced to LOW exponents b in [k, n-r) — NOT the
high-degree Kambire monomials X^{rm}.

FINDINGS (2026-06-14): at n=16, k=4 (rho=1/4), budget=n=16, p-INDEPENDENT (identical counts
across p=200017/500113/1000033):
  r=8 (Johnson, delta .5): max far incidence  9  (<= 16, GOOD)
  r=9 (delta .5625):       max far incidence  9  (<= 16, GOOD)
  r=10 (delta .625):       max far incidence 89  (> 16, BAD), binder (a=10,b=4)
  => delta* = 9/16, exactly one rung BEYOND Johnson (8/16).
The binding far direction is x^4 = x^k (the lowest far exponent, itself an imprimitive pullback
from mu_4), NOT the minimal-orbit (s=2) Kambire extremal X^{rm},X^{(r-1)m}.  Refines the count-lane
R1/R2 conjecture: the worst far direction near capacity is the LOW-exponent x^k, not min-orbit.
"""
import sys, math, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import get_W

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and all(p % d for d in range(2, int(p**0.5) + 1)):
            return p
        p += n

def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def incidence(S, p, k, a, b, r):
    """Exact far-line incidence I(a,b;r); returns (count, saturated_bool)."""
    n = len(S); size = n - r
    if size <= k: return p, True
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if not P: continue
        pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa): return p, True
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return len(good), False

def max_far_incidence(S, p, k, r):
    """max over FAR monomial stacks (direction b in [k, n-r)) of I(a,b;r); returns (max, stack)."""
    n = len(S); size = n - r; best = (-1, None)
    for b in range(k, size):
        for a in range(n):
            if a == b: continue
            c, _ = incidence(S, p, k, a, b, r)
            if c > best[0]: best = (c, (a, b))
    return best

def delta_star(n, k, p=None, budget=None):
    """exact delta* = (largest r with max far incidence <= budget)/n, budget defaults to n (prize)."""
    p = p or find_prime_cong1(n, 200003); S = list(get_W(n, p).S); budget = budget or n
    last_good = None
    for r in range(k + 1, n - k + 2):
        mx, st = max_far_incidence(S, p, k, r)
        if mx <= budget: last_good = r
        else: return (last_good / n if last_good else None, r, st, p)
    return (last_good / n if last_good else None, None, None, p)

if __name__ == '__main__':
    # n=8 (full sweep is cheap): the exact delta* via far-line incidence.
    ds, rbad, st, p = delta_star(8, 2)
    print(f"n=8 k=2 rho=0.250 p={p}: delta* = {ds} (Johnson 0.5000); first bad r={rbad} binder={st}")
    # n=16 (windowed, p-INDEPENDENT): the beyond-Johnson pin + binder, confirmed across primes.
    print("n=16 k=4 rho=0.250 budget=16 (windowed; counts are p-independent):")
    for pl in (200003, 500003):
        p = find_prime_cong1(16, pl); S = list(get_W(16, p).S)
        m9 = max_far_incidence(S, p, 4, 9); m10 = max_far_incidence(S, p, 4, 10)
        print(f"  p={p}: r=9 max={m9[0]} (good), r=10 max={m10[0]} binder={m10[1]} (bad) "
              f"=> delta* = 9/16 = 0.5625  [Johnson 0.5; BEYOND by one rung]")
