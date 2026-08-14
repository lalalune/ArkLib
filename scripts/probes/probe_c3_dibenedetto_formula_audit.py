#!/usr/bin/env python3
"""
C3 audit: is the in-tree diBenedettoSaving formula (10-2t3-t2/2)/72 FAITHFUL to
di Benedetto Thm 3.1, and is 1/24 genuinely the ALGEBRAIC ceiling of the
sum-product/energy family?

di Benedetto et al (arXiv:2003.06165) Thm 3.1: M(H) <~ H^{2689/2880} p^{1/72} for
|H| a multiplicative subgroup. At Burgess edge |H|=p^{1/4} (beta=4):
  H^{2689/2880} * p^{1/72} = H^{2689/2880} * H^{4/72} = H^{2689/2880 + 160/2880}
                           = H^{2849/2880} = H^{1 - 31/2880}.
So saving = 31/2880 at the GENERAL inputs. We reverse-engineer the energy-exponent
parametrization to check the in-tree formula.
"""
from fractions import Fraction as F

# in-tree formula
def saving(t2, t3): return (10 - 2*t3 - F(t2)/2) / 72

# baseline check: general subgroup t2=49/20, t3=4 -> 31/2880 ?
b = saving(F(49,20), 4)
print(f"general-subgroup (t2=49/20, t3=4): saving = {b} = {float(b):.6f}  (target 31/2880={float(F(31,2880)):.6f})  match={b==F(31,2880)}")

# near-Sidon: t2=2, t3=3
ns = saving(2, 3)
print(f"near-Sidon (t2=2, t3=3):           saving = {ns} = {float(ns):.6f}  (target 1/24={float(F(1,24)):.6f})  match={ns==F(1,24)}")

# the HARD FLOORS: t2>=2 (Cauchy-Schwarz: E2 >= |H|^2 ALWAYS), t3>=3 (diagonal: E3>=|H|^3)
# so saving = (10 - 2t3 - t2/2)/72 is MAXIMIZED at the smallest t2,t3 = (2,3):
print()
print("Is (2,3) the maximizer? saving is DECREASING in both t2 and t3:")
print(f"  d(saving)/dt2 = -1/144 < 0,  d(saving)/dt3 = -2/72 = -1/36 < 0")
print(f"  so over the feasible region t2>=2, t3>=3, the MAX is at the corner (2,3) = {float(ns):.6f}")
print()
# can the 2-power structure push BELOW t2=2 or t3=3?  NO: these are universal lower bounds.
print("Can 2-power push t2<2 or t3<3?  NO -- universal floors:")
print("  t2: E2(H) = #{a+b=c+d} >= |H|^2 (the 'diagonal' a=c,b=d gives |H|^2 solutions); so t2>=2 for ANY H.")
print("  t3: E3(H) = #{a+b+c=d+e+f} >= |H|^3 (diagonal pairing); so t3>=3 for ANY H.")
print("  mu_n (2-power) ACHIEVES t2=2 exactly (Sidon mod neg, E2=3n^2-3n) and t3=3 (E3=15n^3).")
print("  => mu_n SATURATES the floor. No subset does better. 1/24 is the family ceiling. PROVEN in _DiBenedettoNearSidonImprovement.diBenedettoSaving_le_ceiling.")
print()
# distance to prize
print(f"PRIZE needs saving = 1/2 = {0.5}.  Best energy-method = 1/24 = {float(ns):.4f}.  Ratio prize/ceiling = {0.5/float(ns):.1f}x short.")

# Could a SHARPER sum-product input (better t2,t3 dependence in the EXPONENT FORMULA, not the floors)
# change the ceiling?  The 3-fold amplification structure is FIXED in di Benedetto.  Higher-fold
# (r-fold) amplification: the analogous saving would be (some affine fn of t_r exponents)/D_r.  The
# RAMANUJAN target 1/2 is the r->infinity / moment-method limit, NOT reachable by ANY fixed-fold
# sum-product amplification with the trivial energy floors.  Konyagin-Shkredov / Rudnev point-plane
# improve the CONSTANT delta for GENERIC sets toward ~1/?, but their improvements are also energy/
# incidence-exponent improvements subject to the SAME diagonal floors -- they raise delta from 0.011
# toward maybe ~0.05-0.1 for generic sets, NEVER to 1/2.  The 1/2 is a different (spectral) mechanism.
print()
print("KONYAGIN-SHKREDOV / RUDNEV note: their improvements push the GENERIC-set sum-product")
print("exponent (few-sums-many-products, point-plane incidences) but are STILL energy/incidence")
print("based, subject to the same diagonal floors t2>=2,t3>=3.  They can raise delta for generic")
print("sets toward ~0.05-0.1 but the SATURATED 2-power subgroup already sits at the 1/24 corner;")
print("there is no further room on the energy side.  The 0.5 prize exponent is SPECTRAL, not sum-product.")
