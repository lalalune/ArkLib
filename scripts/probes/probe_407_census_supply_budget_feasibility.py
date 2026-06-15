#!/usr/bin/env python3
"""
probe_407_census_supply_budget_feasibility.py  (#444 / #371 census-route VIABILITY)

THE UNASKED DECISIVE QUESTION (uncontested lane).
The in-tree census route (CensusDominationWeld.lean) is a PROVEN sufficiency chain:
    epsMCA <= #bad/p <= #alignable/p <= K/p <= eps*  =>  delta* = 1 - r/2^mu.
The weld's hypothesis CensusDomination(dom, k, a0, K) requires the census count K to satisfy
    K / p <= eps*,   where the deployed eps* threshold is   eps* = 2^r * C(2^{mu-1}, r) / p
    (the KKH26 fibre SUPPLY count -- hεstar in kkh26_deltaStar_pin_of_censusDomination).
Equivalently the route needs:
    K  :=  max_{u0,u1}  #alignableSets(band a_bind)   <=   2^r * C(2^{mu-1}, r).         (FEAS)

Nobody has tested (FEAS). c.1007 measured the slack #alignable/#bad (lossy, thickness-invariant);
c.95e633cb0 measured the #bad collapse (thickness-monotone). NEITHER tested whether the census
count K that the route ACTUALLY bounds even fits under the supply budget the SAME weld demands.

TWO OUTCOMES, BOTH REAL:
  (A) K <= 2^r*C(2^{mu-1},r)  at the binding band  => CensusDomination is at least NUMERICALLY
      PLAUSIBLE at the weld budget; the route is internally consistent (points at what to prove).
  (B) K  > 2^r*C(2^{mu-1},r)                       => CensusDomination is FALSE at ITS OWN weld
      budget => the deployed census route is DEAD as stated (the hypothesis over-shoots the very
      supply bound that defines eps*). Refutation-grade.

SEMANTICS: matched EXACTLY to probe_alignment_census.py + UniversalAlignmentLaw.lean.
  domain mu_n = <g>, |mu_n|=n=2^mu, prize prime p~n^beta (PROPER subgroup, m=(p-1)/n>1, NEVER n=q-1).
  m (the smooth multiplier in n=2^mu*m) -- here we take the prize-relevant m=1 (n=2^mu) so k=r-1,
  binding band a_bind = r*m+1 = r+1, k = (r-2)*m+1 = r-1.
  e_j(T) = divided difference [x_{t0..tk}] u_j; S aligned iff all nondeg (k+1)-subtuples share one
  ratio -e0/e1; alignableSets = aligned S (|S|=a) with >=1 nondegenerate tuple.
  K(band a) = MAX over the worst pairs of #alignableSets (the weld quantifies over ALL u0,u1).

We sweep the worst far-line family (char lines [x^A,x^B]) + random pairs as the adversary for K,
and a THICK control (rule 3): if (FEAS) verdict is thickness-INVARIANT, the budget is structural
(not 2-power-essential); if it flips, the 2-power structure is what makes the route (in)feasible.

Exact mod-p, multi-prime incl. non-Fermat. VALIDATION against in-tree c.1007 numbers:
  KKH26 [x^6,x^4] k=3 (mu=3,m=2,r=3) at p=65537: a=4->1792, a=5->336, a=6(bind)->56  (must reproduce).
"""
import itertools, math, sys
from collections import defaultdict


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def next_prime_cong1(n, lo):
    p = lo + (1 - lo % n) % n  # p == 1 mod n
    if p < lo: p += n
    while not is_prime(p):
        p += n
    return p


def find_g(p, n):
    """generator of the order-n subgroup mu_n, proper (m=(p-1)/n>1, never n=q-1)."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    assert m > 1, "PROPER subgroup required (never n=q-1)"
    for h in range(2, 4000):
        x = pow(h, m, p)
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError("no generator")


def divided_diff(pts_idx, u, p):
    total = 0
    for i in pts_idx:
        den = 1
        for j in pts_idx:
            if i == j: continue
            den = den * ((u['x'][i] - u['x'][j]) % p) % p
        total = (total + u['v'][i] * pow(den, -1, p)) % p
    return total


def census_alignable(u0, u1, xs, p, kdim, bands):
    """returns {a: #alignableSets} for char-line/random pairs. EXACT, matches in-tree semantics."""
    n = len(xs)
    U0 = {'x': xs, 'v': u0}
    U1 = {'x': xs, 'v': u1}
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), kdim + 1):
        e0[T] = divided_diff(T, U0, p)
        e1[T] = divided_diff(T, U1, p)

    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if b_ != 0:
            return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'

    out = {}
    for a in bands:
        if a > n: 
            out[a] = 0; continue
        alignable = 0
        for S in itertools.combinations(range(n), a):
            r = None; ok = True; any_nd = False
            for T in itertools.combinations(S, kdim + 1):
                rt = ratio(T)
                if rt is None:
                    continue
                if rt == 'NOROOT':
                    ok = False; break
                any_nd = True
                if r is None:
                    r = rt
                elif r != rt:
                    ok = False; break
            if ok and any_nd:
                alignable += 1
        out[a] = alignable
    return out


def charline(A, B, xs, p):
    return ([pow(x, A, p) for x in xs], [pow(x, B, p) for x in xs])


def supply_budget(r, mu):
    """eps* numerator: 2^r * C(2^{mu-1}, r)  (the KKH26 fibre supply / hεstar bound)."""
    return (2 ** r) * math.comb(2 ** (mu - 1), r)


def main():
    print("=" * 78)
    print("CENSUS SUPPLY-BUDGET FEASIBILITY (FEAS): is K = max_pairs #alignable(a_bind)")
    print("  <=  2^r * C(2^{mu-1}, r)  (the eps* supply the SAME weld requires)?")
    print("=" * 78)

    # -------- VALIDATION block: reproduce the in-tree c.1007 census numbers --------
    print("\n[VALIDATION] m=2 shape, mu=3 (n=8?) -- match probe_alignment_census k=3 numbers.")
    print("  Actually the c.1007 KKH26 [x^6,x^4] k=3 is n=16 (mu=4,m=... ) -- reproduce a=4,5,6.")
    p = 65537; n = 16; kdim = 3
    g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
    u0, u1 = charline(6, 4, xs, p)
    cv = census_alignable(u0, u1, xs, p, kdim, [4, 5, 6])
    print(f"  KKH26 [x^6,x^4] n=16 k=3 p={p}: a=4->{cv[4]}, a=5->{cv[5]}, a=6->{cv[6]}")
    print(f"  EXPECT (c.1007): a=4->1792, a=5->336, a=6->56  =>",
          "MATCH" if (cv[4], cv[5], cv[6]) == (1792, 336, 56) else "MISMATCH")

    # -------- FEASIBILITY block: prize-shape m=1, n=2^mu, k=r-1, a_bind=r+1 --------
    print("\n" + "=" * 78)
    print("[FEASIBILITY] prize shape m=1: n=2^mu, r= depth, k=r-1, binding band a_bind=r+1.")
    print("  K = max over far-line + random adversary pairs of #alignableSets(a_bind).")
    print("  budget = 2^r * C(2^{mu-1}, r).   VERDICT: K <= budget (route viable) / K > budget (DEAD).")
    print("=" * 78)

    for mu in (3, 4):
        n = 2 ** mu
        for beta in (4.0, 4.5):
            lo = int(n ** beta)
            p = next_prime_cong1(n, lo)
            fermat = (p & (p - 1)) == 0 or bin(p - 1).count('1') == 1
            g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
            print(f"\n--- n={n} (mu={mu}), beta={beta}, p={p} "
                  f"{'[non-Fermat]' if not fermat else '[Fermat-ish]'} ---")
            # depths r with k=r-1>=1 and a_bind=r+1<=n
            for r in range(2, n):
                kdim = r - 1
                a_bind = r + 1
                if kdim < 1 or a_bind > n: break
                if r > 2 ** (mu - 1): break  # weld requires r <= 2^{mu-1}
                budget = supply_budget(r, mu)
                # adversary: worst far-line family + a few random pairs
                Kmax = 0; arg = None
                # far-line char pairs: scan a representative worst family (hifreq + antipodal-adjacent)
                cand_lines = [(n // 2 + 1, n // 2 - 1), (n // 2 + 1, n // 2),
                              (n - 1, n - 3), (r + 1, r - 1), (n // 2, n // 4)]
                # plus a small exhaustive-ish scan of low/mid exponent far lines
                for A in range(2, n):
                    for B in range(1, A):
                        if (A, B) not in cand_lines and (A + B) % 2 == 0 and A <= n // 2 + 2:
                            cand_lines.append((A, B))
                seen = set()
                for (A, B) in cand_lines:
                    if (A, B) in seen or A >= n or B >= n or A == B: continue
                    seen.add((A, B))
                    u0, u1 = charline(A, B, xs, p)
                    c = census_alignable(u0, u1, xs, p, kdim, [a_bind])[a_bind]
                    if c > Kmax:
                        Kmax = c; arg = ('line', A, B)
                # random pairs
                import random
                rng = random.Random(hash((p, r)) & 0xffff)
                for _ in range(4):
                    ru0 = [rng.randrange(p) for _ in range(n)]
                    ru1 = [rng.randrange(p) for _ in range(n)]
                    c = census_alignable(ru0, ru1, xs, p, kdim, [a_bind])[a_bind]
                    if c > Kmax:
                        Kmax = c; arg = ('random',)
                verdict = "VIABLE (K<=budget)" if Kmax <= budget else "*** DEAD (K>budget) ***"
                print(f"  r={r} k={kdim} a_bind={a_bind}: K={Kmax} (arg={arg})  budget=2^{r}*C({2**(mu-1)},{r})={budget}"
                      f"   ratio K/budget={Kmax/budget:.3f}  =>  {verdict}", flush=True)

    print("\nDONE.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
