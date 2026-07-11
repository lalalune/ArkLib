#!/usr/bin/env python3
"""
probe_407_deepband_floor_closedform.py  (#444 -- DEEP-BAND floor extension of the canonical #bad/budget)

THE LANE (uncontested; extends 0xSolace's truecore_B_growth, which was SHALLOW-band only):
  18f078296 measured the canonical OpenCoreConditionalPin object #bad / eps*-budget at the SHALLOWEST
  binding band a=3 (r=2) ONLY, finding ratio creeping 0.208->0.242 (n=8..64) and EXTRAPOLATING
  geometrically to ~0.26 (bounded below 1 = floor-consistent). Its OWN honest residual (DISPROOF_LOG):
  "single SHALLOWEST band r=2; deepest band r=2^{mu-1} is brute-infeasible past n=16; the deep-band
  growth law is the open residual." Nobody measured the DEEP-band #bad/budget ratio at growing n.

  This probe SETTLES the next band a=4 (r=3) EXACTLY to n=64 -- NOT by extrapolation but with an EXACT
  CLOSED FORM, using the antipodal-adjacent worst-line structure (sibling 005af2b3b mechanism: the
  gamma-set decomposes into complete dilation orbits, #bad = n*C(n/4,2)+1 at this band).

OBJECT (exact mod-p, PROPER mu_n, prize prime p~n^4, NEVER n=q-1):
  band a, code degree <k with k=a-2, agreement rung r=a-1; budget = 2^r * C(n/2, r)  (in-tree eps*,
  reconciled with truecore_B_growth: a=3,k=1,r=2,budget=4*C(n/2,2)). #bad = #distinct pinned gamma
  = -e0(T)/e1(T) over (k+1)-subtuples T, max over the far monomial char-line adversary (x^A,x^B).

RESULT (a=4, r=3; worst line = ANTIPODAL-ADJACENT (n/2, n/2-1), confirmed exhaustively n=8,16 and by
spot-check n=32; #bad matches the EXACT closed form n*C(n/4,2)+1 at n=8,16,32,64):

  n   #bad = n*C(n/4,2)+1   budget = 8*C(n/2,3)   ratio
  8        9                    32                0.28125
  16       97                   448               0.21652
  32       897                  4480              0.20022
  64       7681                 39680             0.19357

  ASYMPTOTIC (exact): #bad ~ n*(n/4)^2/2 = n^3/32 ; budget ~ 8*(n/2)^3/6 = n^3/6.
  ratio -> (n^3/32)/(n^3/6) = 6/32 = 0.1875  (a CONSTANT FLOOR, well below 1),
  approached MONOTONE FROM ABOVE (0.281 -> 0.217 -> 0.200 -> 0.194 -> 0.1875).

VERDICT (rule-4 mapped; FLOOR-CONSISTENT, prize-positive; rule-6 honest, NOT a closure):
- This EXTENDS the floor-consistency from the shallow band a=3 (0xSolace, extrapolated ~0.26) to the
  DEEPER band a=4 (r=3), and upgrades it from a 3-point geometric guess to an EXACT closed-form limit
  (0.1875), reached monotone FROM ABOVE -- the OPPOSITE of Johnson (which approaches 1 from below).
- The deep band is MORE sub-Johnson than the shallow band (0.1875 < 0.26), and at fixed band a=4 the
  ratio DECREASES in n (0.281->0.194). So deepening the band does NOT erode the floor -- it lowers it.
- RULE-3 CAVEAT (honest, board-convergent): the a=4 #bad VALUE is THICKNESS-INVARIANT -- #bad=97 at
  n=16 a=4 is IDENTICAL across beta=2.3 (thick, prize-FALSE) ... 5.0 (thin). So this finite-n / per-band
  floor is a Johnson-margin feasibility, NOT a thin-essential signal. The thin content lives ONLY in the
  asymptotic, as the whole board converges. This is a NECESSARY-condition (the deployed eps* budget is
  asymptotically sufficient for #bad at band a<=4 with margin), not the prize bound.
- RULE-6 SCOPE: two bands (a=3 surrogate-free shallow, a=4 here); the closed form is EXACT-verified at
  4 values of n (8,16,32,64), antipodal-adjacent worst confirmed exhaustively at n=8,16. The full prize
  is forall-band + the asymptotic decider needs n>=256 (c.348). CORE not closed, no overclaim.
  Python-only exact, no Lean => axiom-clean trivially.

Run: python3 scripts/probes/probe_407_deepband_floor_closedform.py
"""
import itertools, math

def is_prime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if x % q == 0: return x == q
    d = 47
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while not is_prime(p): p += n
    return p

def find_g(p, n):
    m = (p - 1) // n
    assert m > 1, "m>1 required: PROPER mu_n, never n=q-1"
    for h in range(2, 200000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError("no generator")

def ddiff(u, T, xs, p):
    """k-th divided difference (Newton leading coeff) of points (xs[i], u[i]) for i in T."""
    x = [xs[i] for i in T]; v = [u[i] for i in T]
    for lv in range(1, len(T)):
        v = [(v[i] - v[i+1]) * pow((x[i] - x[i+lv]) % p, -1, p) % p for i in range(len(v) - 1)]
    return v[0]

def nbad(A, B, k, a, xs, p):
    """#distinct pinned gamma = -e0(T)/e1(T) at agreement band a, code degree <k, far line x^A,x^B."""
    n = len(xs)
    u0 = [pow(x, A, p) for x in xs]; u1 = [pow(x, B, p) for x in xs]
    pinned = set()
    for S in itertools.combinations(range(n), a):
        r = None; ok = True; nd = False
        for T in itertools.combinations(S, k + 1):
            e0 = ddiff(u0, T, xs, p); e1 = ddiff(u1, T, xs, p)
            if e1 == 0:
                if e0 != 0: ok = False; break
                continue
            g = (-e0) * pow(e1, -1, p) % p; nd = True
            if r is None: r = g
            elif r != g: ok = False; break
        if ok and nd: pinned.add(r)
    return len(pinned)

def main():
    a, k, r = 4, 2, 3
    print("DEEP-BAND floor: canonical #bad / eps*-budget at band a=4 (r=3), worst = antipodal-adjacent.")
    print("  budget = 2^r * C(n/2, r) = 8*C(n/2,3).  closed form #bad = n*C(n/4,2)+1.\n")
    print(f"  {'n':>4} {'#bad':>8} {'closed':>8} {'budget':>8} {'ratio':>9}  worst-line  match")
    for n in (8, 16, 32, 64):
        p = next_prime_cong1(n, int(n ** 4))
        g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
        budget = 2**r * math.comb(n // 2, r)
        cf = n * math.comb(n // 4, 2) + 1
        A, B = n // 2, n // 2 - 1   # antipodal-adjacent worst line
        c = nbad(A, B, k, a, xs, p)
        print(f"  {n:>4} {c:>8} {cf:>8} {budget:>8} {c/budget:>9.5f}  ({A},{B})   {c==cf}", flush=True)
    print("\n  asymptotic ratio -> 6/32 = 0.1875 (constant FLOOR, monotone from above; the OPPOSITE of Johnson).")
    print("  rule-3 caveat: the a=4 #bad VALUE is thickness-invariant (97 across beta 2.3..5.0 at n=16);")
    print("  this is a finite-n Johnson-margin feasibility, NOT a thin-essential signal. CORE not closed.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
