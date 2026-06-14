# The deep-band route cannot pin δ*=Johnson at any supply quality (#389, R3)

`probe_ceiling_supply_sensitivity.py`, exact integers. The deep-band δ* ceiling comes
from ε_mca ≥ P/(q^(m+1)·B) (deep_band_badSet_card_of_supply + ε_mca ≥ badSet/q),
P=C(n,k+m+1), B=supply bound. Best case for the route is B=1.

**Finding.** At the Johnson band m_J (agreement ≈ n√ρ), log2 of the badSet lower bound
at B=1 is log2(P_J) − (m_J+1)·log2 q, which is hundreds–thousands of bits below −128 at
EVERY prize rate, n ∈ [128,2048], q ∈ {n²,n³}. E.g. ρ=1/4, n=1024, q=n²: −4101 bits;
ρ=1/2, n=2048, q=n³: −12211 bits. So the deep-band bad-count bound at Johnson is
≪ 2⁻¹²⁸ even with the smallest conceivable supply.

**Verdict (R3 decided NEGATIVE, structural).** The deep-band route — the fleet's entire
upper-bound machinery (deep-band ceiling, KKH26, the closed-form sharp brackets) — CANNOT
push the δ* ceiling to Johnson at ANY supply quality. Its hard floor is capacity−Θ(1/log n)
(= KKH26, the bracket calibration). The obstruction is the q^(m+1) witness-mass suppression,
NOT the supply size — so improving the supply bound (R3) or moment-sharpening the conversion
(R2) is irrelevant at the Johnson band. Pinning δ* requires a fundamentally different upper
bound that does not pay q^(m+1) — a direct beyond-Johnson bad-count argument. This is the
exact structural reason the wall is the 25-yr beyond-Johnson list-decoding problem.
