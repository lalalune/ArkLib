import math
# The effective conductor bound (KatzEffectiveGaussSum.EffectiveConductorBound) is:
#   q*E_r - n^{2r} <= q*(2r-1)!!*n^r + ERR,   with the conductor reading ERR = cond*sqrt(q).
# The SHARPENED honest finding: cond(M^{*r}) = rank = n^{2r-1} (Swan=0). So ERR = n^{2r-1}*sqrt(q).
# The bound is INFORMATIVE (non-vacuous, i.e. genuinely constrains E_r) only if the ERR term does
# NOT already exceed the LHS trivial range. The trivial bound is ||eta_b||<=n so ||eta_b||^{2r}<=n^{2r}
# and q*E_r - n^{2r} <= (q-1)*n^{2r} < q*n^{2r}. The Weil-II RHS error alone is n^{2r-1}*sqrt(q).
# VACUITY: the error term n^{2r-1} sqrt(q) exceeds the trivial cap q*n^{2r} ?  
#   n^{2r-1} sqrt q  vs  q n^{2r}:  ratio = 1/(n sqrt q) <1. So error < trivial cap. Not THAT vacuity.
#
# The RIGHT vacuity is vs the WICK MAIN TERM (what the bound must prove to beat trivial):
#   does ERR = n^{2r-1} sqrt q  exceed  q*Wick = q (2r-1)!! n^r ?
#   ratio = n^{2r-1} sqrt q / (q (2r-1)!! n^r) = n^{r-1} / ((2r-1)!! sqrt q).
#   >1  <=>  n^{r-1} > (2r-1)!! sqrt q  <=>  (r-1) log n > log((2r-1)!!) + (1/2) log q.
print("EXACT vacuity threshold: ERR=n^{2r-1}sqrt(q) exceeds q*Wick=q(2r-1)!!n^r  <=>")
print("   (r-1) ln n  >  ln((2r-1)!!) + (1/2) ln q")
print()
import math
def dfln(m):
    s=0.0;k=m
    while k>=1: s+=math.log(k);k-=2
    return s
# prize point
n=2.0**30; q=n*2**128
ln_n=math.log(n); ln_q=math.log(q)
print(f"Prize: n=2^30, q=n*2^128, ln n={ln_n:.2f}, ln q={ln_q:.2f}")
print(f"{'r':>4} {'(r-1)ln n':>12} {'ln((2r-1)!!)+0.5ln q':>22} {'vacuous?':>10}")
for r in [1,2,3,4,5,6,10,89]:
    lhs=(r-1)*ln_n
    rhs=dfln(2*r-1)+0.5*ln_q
    print(f"{r:>4} {lhs:>12.1f} {rhs:>22.1f} {'YES' if lhs>rhs else 'no':>10}")
print()
print("So at the prize point the effective-conductor bound (with the HONEST rank-driven conductor")
print("cond=n^{2r-1}) is VACUOUS for all r>=R0 where (r-1)ln n > ln((2r-1)!!)+0.5 ln q.")
# Solve approx: (r-1)*ln n ~ 0.5 ln q  =>  r ~ 1 + 0.5 ln q/ln n. (dropping the slowly-growing df term)
r0=1+0.5*ln_q/ln_n
print(f"Approx threshold r0 ~ 1 + (ln q)/(2 ln n) = {r0:.2f}  (n=2^30, beta~5.27).")
print("The EVT/sup depth is r* ~ ln N ~ ln q ~ 89 >> r0, so the sup-control region is DEEP in vacuity.")
print()
print("KEY: r0 = 1 + (ln q)/(2 ln n) = 1 + beta/2 where q=n^beta. Prize beta=4..5 => r0 = 3..3.5.")
print("So vacuity onset r0 in {3,4} EXACTLY = where char-p excess W_r first appears. Coincidence is structural.")

# ---------------------------------------------------------------------------
# P4 SUMMARY (the answer to "does monodromy control the MAX effectively?"):
#  Effective (Deligne/Weil-II) equidistribution bounds the r-th cumulant deviation
#  from the Wick value (2r-1)!!*n^r by cond(r)*sqrt(q). The HONEST conductor of the
#  r-fold moment sheaf M^{*r} is RANK-DRIVEN: cond(r) = dim H^1_c ~ n^{2r-1}, Swan=0.
#  With that, the error term n^{2r-1}*sqrt(q) ALONE exceeds the entire summed Wick
#  budget q*(2r-1)!!*n^r exactly when  n^{r-1} > (2r-1)!!*sqrt(q)  (product form).
#  Taking logs at q=n^beta, the VACUITY ONSET is  r0 = 1 + beta/2.
#  Prize beta=4..5 => r0 in {3, 3.5} => VACUOUS at r=4 = exactly the moment order
#  where char-p additive energy excess W_r first appears (E_3 p-invariant; E_4 fails).
#  EVT/sup control of M=max||eta_b|| needs depth r* ~ ln N ~ ln q ~ 89 >> r0, deep in
#  the vacuous region. So monodromy controls the AVERAGE moment to r<=3 only; the MAX
#  is unreachable. VERDICT: reduces-to-bgk. The Lean file
#  Frontier/_C5MonodromyMaxControlScissors.lean formalizes this (axiom-clean).
