# probe_407_close_countlane_VERDICT.py
#
# VERDICT probe for the OPEN ITEM: does E2VanishRigidityModP's fold/resultant machinery
# prove the count-lane D-height bound  log2(D) = O(n log n)  needed for the floor pigeonhole?
#
# Findings assembled from probe_407_close_countlane_{D_height, D_singleresultant, D_growth}
# and the exact sumset-polynomial heights (/tmp/gr_fast2.py):
#
#   (1) PER-CONFIG height (what E2 actually bounds).  e2_extra_solution_threshold says:
#       a NEW mod-p e_2=0 solution at config U forces  p <= (card U^2 + card U)^{n/2}
#       <= (n^2+n)^{n/2}.  This is a bound on EACH bad prime's SIZE, uniform over configs,
#       because the FOLD has l1 mass <= n^2+n REGARDLESS of which config U.
#       -> gives (H1):  max bad prime <= (n^2+n)^{n/2} = 2^{O(n log n)}.
#
#   (2) The count-lane bad-prime SET is a UNION over 2^{Theta(n)} configs.  Each config
#       contributes the odd primes ===1 mod n dividing its own gcd(N(sum u),N(sum u^3)),
#       each <= the per-config threshold.  Measured FULL union:
#          n=8 : 0 candidate primes (every N(sum u) is a power of 2)
#          n=16: 11 candidate primes {17,97,113,193,241,337,353,401,433,577,881}; ACTUAL bad = 0
#       -> #distinct candidate primes (n=16) = 11 <= n log n = 64.  Holds for n=8,16.
#
#   (3) The SINGLE-integer "D".  For (H2) #bad primes <= log2(D), D must be ONE integer
#       of height 2^{O(n log n)} that every bad prime divides.  Two candidate single
#       integers, and their EXACT heights:
#         (a) The sumset polynomial G_r(gamma)=prod_J(gamma-sigma_J): integer, monic,
#             deg=|Sigma_r|.  Heights (exact):
#               mu_8  r=2 (n=16): log2 ht 11.08   r=3: 24.45   r=4: 34.31
#               mu_16 r=2 (n=32): log2 ht 51.89   r=3: 301.66
#             -> G_r height is NOT O(n log n): at n=32 r=3 it is 301.66 >> 160 = n log n,
#                and GROWS with r (and with deg=|Sigma_r| ~ 2^{Theta(s)}).
#             So G_r itself is the WRONG single integer for the pigeonhole.
#         (b) The PER-CONFIG fold/resultant N_U = Res(e2Fold_U, Phi_n): height
#             <= (n^2+n)^{n/2} = 2^{O(n log n)} PER U, but there are 2^{Theta(n)} of them;
#             D = prod_U N_U has height 2^{Theta(n)} * O(n log n) -- NOT O(n log n).
#
# This probe RE-DERIVES (1)-(3) compactly and prints the precise verdict numbers, so the
# claim "#bad primes <= log2(D) = O(n log n)" can be checked against what the machinery
# actually delivers.

import math
from itertools import combinations, product
import sympy as sp

def per_config_threshold(n):
    return (n//1, (n//2) * math.log2(n*n + n))   # log2((n^2+n)^{n/2})

def full_union_candidate_primes(n, sizes):
    HALF = n//2
    z = sp.symbols('z'); Phi = sp.Poly(sp.cyclotomic_poly(n, z), z)
    def vec(exps):
        v=[0]*HALF
        for e in exps:
            e%=n
            if e<HALF: v[e]+=1
            else: v[e-HALF]-=1
        return v
    def poly(v): return sp.Poly(sum(int(c)*z**l for l,c in enumerate(v)),z)
    def Nrm(v): return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))
    union=set(); per_config_logmax=0.0
    for size in sizes:
        for pr in combinations(range(HALF), size):
            for signs in product([0,1],repeat=size):
                exps=[pr[i]+(HALF if signs[i] else 0) for i in range(size)]
                a=vec(exps); b=vec([3*e for e in exps])
                if all(c==0 for c in a) or all(c==0 for c in b): continue
                Na,Nb=Nrm(a),Nrm(b); mx=max(Na,Nb)
                if mx>1: per_config_logmax=max(per_config_logmax, math.log2(mx))
                g=sp.gcd(Na,Nb)
                if g>0:
                    for q,_ in sp.factorint(g).items():
                        if q%2==1 and q%n==1: union.add(int(q))
    return sorted(union), per_config_logmax

if __name__ == '__main__':
    print("="*78)
    print("VERDICT: count-lane D-height for the floor pigeonhole")
    print("="*78)

    print("\n(1) PER-CONFIG threshold log2((n^2+n)^{n/2}) [= what E2 proves, uniform over U]:")
    for n in [8,16,32]:
        _, l = per_config_threshold(n)
        print(f"    n={n:>3}: (n/2)log2(n^2+n) = {l:.1f}   (= O(n log n), this IS the e2-species bound)")

    print("\n(2) FULL union of candidate primes (all sizes), and per-config max log2 N:")
    for n,sizes in [(8,list(range(2,5))),(16,list(range(2,9)))]:
        u,pcl = full_union_candidate_primes(n,sizes)
        print(f"    n={n:>3}: #distinct candidate primes = {len(u)} (<= n log n = {n*math.log2(n):.0f}); "
              f"per-config max log2 N = {pcl:.1f}")
        print(f"           primes = {u}")

    print("\n(3) SINGLE-integer sumset polynomial G_r height (exact, /tmp/gr_fast2.py):")
    gr = {("n=16",2):11.08,("n=16",3):24.45,("n=16",4):34.31,
          ("n=32",2):51.89,("n=32",3):301.66}
    nlogn={"n=16":64.0,"n=32":160.0}
    for (lab,r),l2 in gr.items():
        flag = "<= n log n" if l2<=nlogn[lab] else ">> n log n  (FAILS as single-D)"
        print(f"    {lab} r={r}: log2 height(G_r) = {l2:.1f}  vs  n log n = {nlogn[lab]:.0f}   {flag}")

    print("""
================================ VERDICT =====================================
 - (H1) "max bad prime <= 2^{O(n log n)}" : PROVEN-species (e2_extra_solution_threshold,
   uniform per-config fold l1 <= n^2+n).  The count-lane individual conditions e_1=0,
   e_3=0 are LINEAR (fold l1 <= n), even cheaper; the e_2-VALUE obstruction is the
   quadratic one (l1 <= n^2+n).  So EACH count-lane bad prime is <= (n^2+n)^{n/2}.

 - (H2) "#distinct bad primes <= log2(D) = O(n log n)" : NOT delivered by the E2
   machinery as stated.  E2 bounds each bad prime's SIZE, not the COUNT.  The count-lane
   bad-prime set is a UNION over 2^{Theta(n)} configs; the only single integers available
   are (a) G_r, whose height is NOT O(n log n) (n=32 r=3 -> 301.66 >> 160, and grows with
   r since deg=|Sigma_r| ~ 2^{Theta(s)}), or (b) prod_U N_U, height 2^{Theta(n)}.

 - So "#floor-bad primes <= log2(D)" with log2(D)=O(n log n) is NOT a consequence of the
   proven e2-rigidity species.  It would require a SHARPER fact: that the count-lane bad
   primes all divide a SINGLE integer of height 2^{O(n log n)} -- which the sumset
   polynomial G_r does NOT provide (too big), and the per-config product does NOT provide
   (union, not single).  EMPIRICALLY the candidate-prime count is tiny (0, 11) and well
   below n log n at n=8,16, but that is an empirical observation, NOT the size-bound
   pigeonhole the directive describes.
=============================================================================
""")
