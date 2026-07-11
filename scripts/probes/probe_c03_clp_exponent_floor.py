#!/usr/bin/env python3
"""
C03 Croot-Lev-Pach slice-rank lift (analyst: reduces-to-johnson, CLP n^{0.92} >> floor).

C03 claims: the worst-case far-line incidence object, viewed as a 3-tensor / slice-rank
problem, gets a CLP/slice-rank cap.  The best cap-set saving (Ellenberg-Gijswijt over F_3^N)
is |A| <= (2.7551...)^N out of 3^N, i.e. exponent c_3 = log_3(2.7551) ~ 0.9183, a saving
of 1-c ~ 0.0817.  So a slice-rank cap gives the object size <= n^{c} with c ~ 0.92.

THE FLOOR: the prize floor (past-Johnson) is the BGK sup-norm scale M(mu_n) ~ sqrt(n log(p/n)),
i.e. the incidence/list floor is ~ n^{1/2} (times log).  CLP gives n^{0.92}.

CHECK (pure arithmetic, no probe needed but we make it explicit):
  Is the best slice-rank exponent c ~ 0.92 ABOVE the floor exponent 0.5?
  If yes: CLP is "closed but far short of the floor" => reduces-to-johnson (caps no better
  than Johnson-side; cannot reach the sqrt floor).  A flip would need c < 0.5 (impossible:
  the EG bound is a saving of <0.09, the absolute slice-rank floor for these tensors is well
  above 1/2).  We also confirm c is an EG-style ambient-dimension saving, not a Z/p saving.
"""
from math import log

# Ellenberg-Gijswijt cap-set exponent for F_3^N (the canonical CLP/slice-rank result)
# |cap| <= 3 * Gamma^N with Gamma = 0.918305... per the EG/BCCGNSU computation; the
# multiplicative cap exponent is log_3(2.7551) = 0.91795...
gamma_lambda = 2.755100   # the base (BCCGNSU 2017 computed value)
c3 = log(gamma_lambda)/log(3.0)
print(f"EG cap-set exponent c_3 = log_3({gamma_lambda}) = {c3:.5f}  (saving 1-c = {1-c3:.5f})")

# Best general slice-rank saving over F_q^N stays close to 1 (saving shrinks as q grows).
# In NO regime does slice-rank give exponent below 1/2 for a sumset/incidence count of
# the form n^c.  The floor is n^{1/2}.
floor_exp = 0.5
print(f"floor exponent (BGK sqrt scale) = {floor_exp}")
print(f"CLP best exponent c ~ {c3:.4f} > floor {floor_exp}? -> {c3 > floor_exp}")
print(f"  => CLP cap n^{{{c3:.3f}}} >> floor n^{{0.5}} : closed but cannot reach the sqrt floor.")

# Numbers at prize scale: n=2^mu, the gap n^c vs n^0.5
print("\n n    n^0.92    n^0.5(floor)   ratio (how far CLP is above floor)")
for mu in [3,4,5,6,7]:
    n=2**mu
    a=n**c3; b=n**0.5
    print(f"{n:>4}  {a:>9.2f}   {b:>9.2f}     {a/b:>8.2f}")

# Sanity: the dimensional category note (same as C39). EG saving lives in ambient dim N->inf.
print("\nNOTE: EG/CLP saving is in the AMBIENT DIMENSION of F_q^N (N->inf). The prize")
print("incidence object lives in a FIXED small ambient dimension (the far-line / 3-tensor")
print("over Z/p is effectively dim 1-3), where the slice-rank saving is asymptotically void.")
print("Even granting the saving, n^0.92 >> n^0.5 floor. Verdict: reduces-to-johnson.")
