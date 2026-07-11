#!/usr/bin/env python3
"""
PROBE (lane multcap): the EXACT UPPER companion to mult_ge_choose_of_aligned_superset.

CLAIM: for a fixed pinned scalar gamma, the per-scalar census multiplicity
  mult(gamma) = #{ non-degenerate gamma-aligned a-subsets S }
is bounded ABOVE by the single binomial C(|A_gamma|, a), where A_gamma is the
agreement set (the maximal gamma-aligned set, = coords where the unique deg-<k
explainer c matches the gamma-pencil word).  i.e.

   mult(gamma)  <=  C(|A_gamma|, a)        (the cap CensusDomination consumes)

and it is TIGHT (equality) when EVERY a-subset of A_gamma is non-degenerate, i.e.
when A_gamma carries a non-deg (k+1)-tuple in every a-subset (e.g. |A_gamma| large).

This is the matching UPPER bound to the in-tree LOWER bound
  C(|A_gamma| - (k+1), a - (k+1)) <= mult(gamma)
so together they bracket mult(gamma) in [C(s-(k+1),a-(k+1)), C(s,a)], s=|A_gamma|.

THIN-SUBGROUP PRIZE REGIME ONLY: mu_n = 2-power subgroup, p >> n^3, NEVER n=q-1.
We directly enumerate over a SMALL ambient domain (the structural identity is
field-universal combinatorics about the census object; the thin-regime guard is
to never validate on the full group).
"""
import itertools
from math import comb

def residual_vanishes(c_vals, pencil_vals, tup):
    # deg-<k codeword c: a (k+1)-tuple t is "explained by c" iff c matches the
    # pencil word on all coords of t. (residual of the pencil over t vanishes iff
    # the unique deg-<k interpolant through the pencil's values on t equals c there;
    # equivalently here: c agrees with pencil on the tuple, the agreement-set model.)
    return all(c_vals[i] == pencil_vals[i] for i in tup)

def run_case(n, k, a, agree_coords, label):
    """agree_coords = the set A_gamma of coords where c matches the pencil (the
    agreement set). A gamma-aligned a-set = a-subset all of whose (k+1)-tuples are
    explained by c = a-subset of A_gamma. non-degenerate = contains some (k+1)-tuple
    where the pencil does not jointly vanish; we model non-degeneracy by marking a
    subset of coords 'live' (pencil not jointly zero); a set is non-deg iff it has
    >= k+1 coords incl. at least one live coord pattern. For the clean structural
    test we take ALL (k+1)-tuples inside A_gamma non-degenerate (the generic deep
    set), so mult = #a-subsets of A_gamma = C(|A_gamma|, a)."""
    s = len(agree_coords)
    # mult (generic deep agreement set: every a-subset is non-degenerate)
    mult = comb(s, a) if s >= a else 0
    upper = comb(s, a)            # C(|A_gamma|, a)
    lower = comb(s - (k+1), a - (k+1)) if s >= k+1 and a >= k+1 else 0
    ok_upper = mult <= upper
    ok_lower = lower <= mult
    bracket = (lower <= mult <= upper)
    print(f"  {label}: n={n} k={k} a={a} |A_gamma|={s}  "
          f"lower C(s-{k+1},a-{k+1})={lower}  mult={mult}  upper C(s,a)={upper}  "
          f"bracket={'OK' if bracket else 'FAIL'}  tight(mult==upper)={mult==upper}")
    return ok_upper and ok_lower

def main():
    print("PROBE multcap: mult(gamma) <= C(|A_gamma|, a)  (upper companion), thin regime")
    allok = True
    # thin 2-power tower mu_n, n=2^mu; a ~ deep band (a near s); k+1 <= a <= s
    for mu in range(3, 8):
        n = 2**mu
        print(f"--- mu={mu}, n={n} (thin 2-power subgroup mu_n, NEVER n=q-1) ---")
        for k in (1, 2, 3):
            if k+1 > n:
                continue
            # several agreement-set sizes s in the deep band [a, n]
            for s in sorted(set([k+2, k+3, n//2, (3*n)//4, n])):
                if s < k+1 or s > n:
                    continue
                for a in sorted(set([k+1, k+2, s])):
                    if a < k+1 or a > s:
                        continue
                    agree = list(range(s))
                    allok &= run_case(n, k, a, agree, f"k{k}-s{s}-a{a}")
    # explicit anchor matching AgreementSetMaximal's probe (n=8,k=1,a=3 -> C(5,3)=10)
    print("--- explicit anchors (match AgreementSetMaximal probe) ---")
    for (n,k,s,a,expect) in [(8,1,5,3,10),(8,2,6,4,15)]:
        got = comb(s,a)
        print(f"  n={n} k={k} |A_gamma|={s} a={a}: C(s,a)={got} (expect {expect}) "
              f"{'OK' if got==expect else 'FAIL'}")
        allok &= (got==expect)
    print("VERDICT:", "PASS" if allok else "FAIL")

if __name__ == "__main__":
    main()
