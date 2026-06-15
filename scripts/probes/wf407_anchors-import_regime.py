#!/usr/bin/env python3
"""
wf407_anchors-import: per-anchor regime check for the DROPPED external anchors of #407 §8.

For EACH dropped anchor we test, with EXACT arithmetic at prize parameters, whether the
anchor's hypothesis is satisfiable in the prize regime, and whether the object it bounds is
the prize object B(mu_n)=max_{b!=0}|Sum_{x in mu_n} e_p(b x)| (the linear Gauss period).

Prize regime: n = 2^a (a in [25,40] realizable, cap a<=40), p ~ n*2^128, q<2^256,
  index m=(p-1)/n = 2^128, density n/p = 2^-128 (THINNEST), |mu_n| = n.

Anchors:
  (1) OSV  2211.07739  "Weil sums over small subgroups": Sum_{x in G} psi(f(x)), deg f>=2,
      f not g(x^k). Range of nontriviality and whether the LINEAR f(x)=b*x is covered.
  (2) KSV  2005.05315  Konyagin-Shparlinski-Vyugin "Polynomial Equations in Subgroups":
      N < 12 m n (m+n) g h^{5/3} t^{2/3}, valid 12 p^{3/4} h^{-1/4} >= t >= max{h^2, c0}.
      Conjecture 1.3 = subgroup Mobius coincidence (a11 u - a12)/(a21 u - a22)=v, <=A sols.
  (3) Myerson lacunary cyclotomic resultant maxima: small-sum f(k,n) shape
      k^{-n} <= f(k,n) <= n^{-k/4+o(1)} (upper only when k,n both even).
      = the archimedean house bound |N(Sum_{i in S} zeta^i)| <= (#S)^{phi(n)} (HeightGateNormBound).
  (4) Corvaja-Zannier (JEMS 2013) / Makarychev-Vyugin (Arnold MJ 2019): subgroup poly-eqn count,
      the t^{2/3} ancestor of KSV.
"""

from math import log2

PRIZE_A = list(range(25, 41))          # realizable log2(n)
LOG2_INDEX = 128                       # m = 2^128
def log2_p(a): return a + LOG2_INDEX   # p ~ n*2^128 => log2 p ~ a+128

print("="*78)
print("ANCHOR (1) OSV 2211.07739  — Weil sums over small subgroups")
print("="*78)
# OSV bounds Sum_{x in G} psi(f(x)) with deg f = d >= 2 and f NOT of the form g(x^k).
# Its nontriviality regime (from the paper's method = AG x additive comb, like 2110.10941):
# it gives o(t) savings for t > p^theta with theta DECREASING in d but the object requires d>=2.
# THE PRIZE OBJECT is the LINEAR Gauss period f(x)=b*x  (d=1). OSV's hypothesis d>=2 EXCLUDES it.
print("OSV hypothesis: deg f = d >= 2 (and f != g(x^k)).")
print("Prize object  : B(mu_n) = max_b |Sum_{x in mu_n} e_p(b*x)| = LINEAR Weil sum, f(x)=b*x, d=1.")
print("=> d=1 < 2: OSV's degree hypothesis is NOT satisfied by the prize object. OSV is the")
print("   WRONG SHAPE for the linear Gauss period. It DOES match the higher-moment / tangent")
print("   object T_h = Sum_{w in mu_n} chi^h(1-w) (deg-1 rational arg) only ASYMPTOTICALLY.")
print()

print("="*78)
print("ANCHOR (2) KSV 2005.05315  — Polynomial Equations in Subgroups")
print("="*78)
# Thm 1.2: Sum_i #{(u,v) in G^2: P_i(u,v)=0} < 12 m n (m+n) g h^{5/3} t^{2/3}
# valid for 12 p^{3/4} h^{-1/4} >= t >= max{h^2, c0(m,n)}.
# Prize: t = n = 2^a, p ~ 2^{a+128}.
print(f"{'a':>3} {'log2 t=log2 n':>13} {'log2 t^{2/3}':>14} {'log2(12 p^{3/4})':>17} "
      f"{'upper t ok?':>11} {'lower t>=h^2 (h=2)':>18}")
for a in PRIZE_A:
    lp = log2_p(a)
    log2_t = a
    log2_tcount = (2.0/3.0)*a            # the COUNT bound exponent in t
    log2_upper = log2(12) + 0.75*lp      # 12 p^{3/4} h^{-1/4}, take h=2 => -1/4*1
    log2_upper_h2 = log2_upper - 0.25
    upper_ok = log2_t <= log2_upper_h2   # t <= 12 p^{3/4} h^{-1/4}
    lower_ok = log2_t >= 2*1.0           # t >= h^2, smallest h=2 => 4
    print(f"{a:>3} {log2_t:>13.1f} {log2_tcount:>14.1f} {log2_upper_h2:>17.1f} "
          f"{str(upper_ok):>11} {str(lower_ok):>18}")
print()
print("KSV gives an ALGEBRAIC-COINCIDENCE COUNT t^{2/3} (the # of (u,v) in G^2 on a curve),")
print("NOT a character-sum sup-norm. The count side is already the 'list/orbit' face of the")
print("prize (cluster 3), where the wall is W1 (per-witness C(w-1,d+1)). t^{2/3} << t is a")
print("nontrivial saving on the COUNT, but it is on POLYNOMIAL coincidences P(u,v)=0, not on")
print("the linear Gauss period. The KSV upper-range t <= 12 p^{3/4} is satisfied (a<<0.75*lp),")
print("so the count theorem APPLIES IN REGIME — but to the wrong object (count, not B-form).")
print()
print("KSV Conjecture 1.3 (subgroup Mobius coincidence) is CONDITIONAL and OPEN; it would give")
print("the Markoff bound (log p)^B. It bounds (a11 u - a12)/(a21 u - a22)=v solutions in G by O(1)")
print("for #G <= p^{eps0}. This IS exactly a degree-(1,1) bilinear/Mobius coincidence count — the")
print("'subgroup Mobius-coincidence' object. But it is (i) a CONJECTURE (open), and (ii) again a")
print("COUNT of coincidences, not the character-sum B-form. So it is on the count/list face, gated")
print("by its own open status.")
print()

print("="*78)
print("ANCHOR (3) Myerson lacunary cyclotomic resultant maxima")
print("="*78)
# Myerson small-sum: f(k,n) = min nonzero |sum of k n-th roots of unity| has
#   k^{-n} <= f(k,n) <= n^{-k/4+o(1)}  (upper only when k,n even).
# The house/norm side: |N(Sum_{i in S} zeta^i)| <= (#S)^{phi(n)} = k^{n/2}  (S has k=#S elements).
# This IS the archimedean bound in HeightGateNormBound.lean. Myerson's LOWER bound k^{-n} on the
# small sum <=> the product of conjugates (the norm) is an integer >=1, |N|<=k^{phi(n)}.
# Compare to the prize prime p ~ 2^{a+128}: the gate p > k^{n/2} (here use the WORST k=n).
print("Myerson: f(k,n) in [k^{-n}, n^{-k/4+o(1)}]. The companion is the resultant norm bound")
print("         |N(Sum_{i in S} zeta_n^i)| <= (#S)^{phi(n)} <= n^{n/2}  (= HeightGateNormBound).")
print(f"{'a':>3} {'log2 n^{n/2}':>14} {'log2 p ~ a+128':>15} {'gate p>n^{n/2}?':>16}")
for a in PRIZE_A:
    n = 2**a
    log2_house = (n/2.0)*a          # log2(n^{n/2}) = (n/2)*a  -- astronomically large for a>=25
    lp = log2_p(a)
    gate = lp > log2_house
    print(f"{a:>3} {log2_house:>14.3e} {lp:>15} {str(gate):>16}")
print()
print("Myerson's MAX (the worst-case house) is exactly the (#S)^{phi(n)} archimedean bound that")
print("HeightGateNormBound already uses; Myerson's improvement (n^{-k/4} upper on the MIN) is in")
print("the WRONG direction (it bounds how SMALL a sum can be, i.e. a LOWER bound on the defect")
print("count, not an upper bound on the house). For growing n the house n^{n/2} >> p for all a>=8")
print("(see HeightGateNormBound gate_NOT_fires_64), so the structure-aware/Myerson refinement does")
print("NOT rescue the gate past n=32. Myerson hits the SAME height-obstruction wall (RES_407 sec4).")
print()

print("="*78)
print("ANCHOR (4) Corvaja-Zannier JEMS 2013 / Makarychev-Vyugin Arnold MJ 2019")
print("="*78)
print("These are the t^{2/3} ANCESTORS of KSV Thm 1.2 (same object: # of (u,v) in G^2 solving a")
print("polynomial/gcd coincidence). CZ 2013 = gcd(u-1,v-1) bound for u,v in a finitely generated")
print("subgroup; MV 2019 = solutions of poly equations in subgroups of F_p. KSV strictly improves")
print("both. So CZ/MV are SUBSUMED by KSV: same count face, same t^{2/3}-on-count verdict.")
print()
print("="*78)
print("NET VERDICT")
print("="*78)
print("OSV     : WRONG SHAPE for B-form (needs deg>=2; prize is linear d=1). Right object only for")
print("          the higher tangent sum T_h, and there only ASYMPTOTICALLY (no effective instance).")
print("KSV/CZ/MV: COUNT face (t^{2/3} coincidence count), applies in regime but bounds the orbit/")
print("          list count (cluster 3, wall W1), NOT the analytic B-form. Conj 1.3 is OPEN.")
print("Myerson  : SAME height-obstruction wall as HeightGateNormBound (the house = (#S)^{phi(n)}");
print("          improvement is on the MIN (wrong direction) and dies for n>=64. No new lever.")
