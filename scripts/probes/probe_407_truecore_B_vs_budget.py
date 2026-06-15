#!/usr/bin/env python3
"""
probe_407_truecore_B_vs_budget.py  (#444 -- the CANONICAL open core, not the census surrogate)

The deployed CANONICAL open core (OpenCoreConditionalPin.lean) is
    WorstCaseIncidenceBounded C delta B :  forall stacks u, #{gamma : mcaEvent C delta (u0) (u1) gamma} <= B
with the pin requiring B/q <= eps*, eps* = 2^r*C(2^{mu-1},r)/q. The OBJECT is
    B := max over stacks u of  #bad(u)  =  #distinct pinned gamma at the binding band.
NOTE: B uses #bad (DISTINCT pinned gamma), NOT #alignable (alignable a-SETS). The census route
(probe ...supply_budget...) bounds B via #bad <= #alignable <= K, and I showed K > budget (census DEAD).
But #bad <= #alignable is LOSSY (c.1007: up to 112x). So the TRUE core B could still be <= budget even
though the census surrogate K is not. THIS measures B DIRECTLY -- the actual prize obligation.

QUESTION (decisive, uncontested): at the binding window band, is
    B = max_stack #distinct-bad-gamma  <=  2^r * C(2^{mu-1}, r)  ?      (TRUE-CORE-FEAS)
  (A) B <= budget  => the canonical core is NUMERICALLY FEASIBLE at the weld budget even though the
      census surrogate is not -- the route should target #bad DIRECTLY (not #alignable), and the
      target is plausible (rederives + sharpens the c.1007 "target #bad directly" recommendation
      into a quantitative feasibility statement).
  (B) B > budget   => even the TRUE core overflows eps* at the binding band => the deployed eps*
      threshold itself is too small at that radius (the pin's budget is unmet by the real object).

SEMANTICS matched to UniversalAlignmentLaw: #bad(band a) = #distinct gamma s.t. SOME a-set is
gamma-aligned with a nondegenerate tuple (= #distinct ratios -e0(T)/e1(T) that get "pinned" by an
alignable a-set). Exact mod-p, PROPER mu_n (m>1, never n=q-1), prize primes incl. non-Fermat.
Adversary for the max: exhaustive char-line pairs (n=8) / worst-line family + random (n=16).
"""
import itertools, math, sys, random


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n
    if p < lo: p += n
    while not is_prime(p):
        p += n
    return p


def find_g(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    assert m > 1
    for h in range(2, 6000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError


def divided_diff(pts_idx, vx, vv, p):
    total = 0
    for i in pts_idx:
        den = 1
        for j in pts_idx:
            if i == j: continue
            den = den * ((vx[i] - vx[j]) % p) % p
        if den % p == 0:
            return None
        total = (total + vv[i] * pow(den, -1, p)) % p
    return total


def nbad_at_band(u0, u1, xs, p, kdim, a):
    """#distinct pinned gamma = #distinct ratios that an alignable a-set pins (the #bad object)."""
    n = len(xs)
    if a > n: return 0
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), kdim + 1):
        e0[T] = divided_diff(T, xs, u0, p)
        e1[T] = divided_diff(T, xs, u1, p)

    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if a_ is None or b_ is None: return None
        if b_ != 0:
            return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'

    pinned = set()
    for S in itertools.combinations(range(n), a):
        r = None; ok = True; any_nd = False
        for T in itertools.combinations(S, kdim + 1):
            rt = ratio(T)
            if rt is None: continue
            if rt == 'NOROOT':
                ok = False; break
            any_nd = True
            if r is None: r = rt
            elif r != rt:
                ok = False; break
        if ok and any_nd:
            pinned.add(r)
    return len(pinned)


def charline(A, B, xs, p):
    return ([pow(x, A, p) for x in xs], [pow(x, B, p) for x in xs])


def maxB(xs, p, kdim, a, n, exhaustive):
    Bmax = 0; arg = None
    if exhaustive:
        lines = [(A, B) for A in range(1, n) for B in range(0, A)]
    else:
        lines = [(n // 2 + 1, n // 2 - 1), (n // 2 + 1, n // 2), (n - 1, n - 3),
                 (n // 2, n // 4), (a, a - 2)]
        for A in range(2, n // 2 + 3):
            for B in range(1, A):
                lines.append((A, B))
    seen = set()
    for (A, B) in lines:
        if (A, B) in seen or A >= n or A == B: continue
        seen.add((A, B))
        u0, u1 = charline(A, B, xs, p)
        c = nbad_at_band(u0, u1, xs, p, kdim, a)
        if c > Bmax: Bmax = c; arg = (A, B)
    rng = random.Random(999 ^ p)
    for _ in range(6):
        ru0 = [rng.randrange(p) for _ in range(n)]
        ru1 = [rng.randrange(p) for _ in range(n)]
        c = nbad_at_band(ru0, ru1, xs, p, kdim, a)
        if c > Bmax: Bmax = c; arg = ('rand',)
    return Bmax, arg


def main():
    print("=" * 84)
    print("TRUE CORE: B = max_stack #DISTINCT-bad-gamma at binding band, vs eps* budget 2^r*C(2^{mu-1},r)")
    print("  (#bad direct, NOT the lossy #alignable surrogate). m=1 prize shape: k=r-1, a_bind=r+1.")
    print("=" * 84)
    # n=8: exhaustive over ALL char-lines (binding bands fast). n=16: strong worst-line family
    # (exhaustive #bad over a=r+1 sets per line; deepest bands capped via the focused family).
    n16_lines = [(9, 7), (10, 8), (9, 8), (8, 4), (15, 13), (10, 6), (12, 8), (8, 6),
                 (7, 5), (6, 4), (11, 9), (14, 10)]
    for mu in (3, 4):
        n = 2 ** mu
        exhaustive = (n == 8)
        for beta in (4.0, 4.5):
            p = next_prime_cong1(n, int(n ** beta))
            fermat = bin(p - 1).count('1') == 1
            g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
            print(f"\n--- n={n} (mu={mu}), beta={beta}, p={p} "
                  f"{'[non-Fermat]' if not fermat else '[Fermat]'} {'EXHAUSTIVE' if exhaustive else 'worst-family'} ---")
            for r in range(2, n):
                kdim = r - 1; a = r + 1
                if a > n or r > 2 ** (mu - 1): break
                budget = (2 ** r) * math.comb(2 ** (mu - 1), r)
                if exhaustive:
                    B, arg = maxB(xs, p, kdim, a, n, True)
                else:
                    B = 0; arg = None
                    for (A, Bb) in n16_lines:
                        if A >= n or A == Bb: continue
                        u0, u1 = charline(A, Bb, xs, p)
                        c = nbad_at_band(u0, u1, xs, p, kdim, a)
                        if c > B: B = c; arg = (A, Bb)
                v = "FEASIBLE (B<=budget)" if B <= budget else "*** B>budget ***"
                print(f"  r={r} k={kdim} a={a}: B={B} (worst={arg}) budget={budget} "
                      f"ratio={B/budget:.3f} => {v}", flush=True)
    print("\nCompare to the census K (alignable) overflow: if B<=budget where K>budget, the route's")
    print("infeasibility is purely the #bad<=#alignable LOSS (c.1007), and #bad direct is the right target.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
