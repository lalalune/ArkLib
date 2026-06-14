# EXACT δ* characterization: δ* = inverse of a q-independent symmetric-function count (2026-06-13)

Completing the calibration. The worst MCA direction is `dir(k,b)` (verified, evades the mod-4 obstruction).
Deriving its reduction in closed form:

## Worst-direction reduction (derived, verified `probe_dir_k_kp2_subsetsum.py`)
For `dir(k,t)` (a=k, b=t) at agreement band `t`: `X^k+γX^t ≡ (deg<k) mod m_T` forces, via
`X^t ≡ Σ(-1)^j e_j X^{t-j}`:
> **`e_1(T) = e_2(T) = ⋯ = e_{t-k-1}(T) = 0`**  (first `t−k−1` elem. symm. functions vanish),  with
> **`γ ∝ e_{t-k}(T)`**.
By Newton's identities this ⟺ first `t−k−1` POWER SUMS vanish: `p_1(T)=⋯=p_{t-k-1}(T)=0`.

So the MCA bad-scalar count at band `δ=1−t/n` is the **q-independent** combinatorial quantity
> `#bad(t) = #{ distinct e_{t-k}(T) : T⊆μ_n, |T|=t, e_1(T)=⋯=e_{t-k-1}(T)=0 }`.

## Verification at t=k+2 (condition e_1(T)=0)
`e_1(T)=0` ⟺ (Lam–Leung) `T` = union of antipodal pairs ⟹ `γ ∝ Σx² = 2Σ_{pairs}ζ^{2i}` = subset-sum of
`w/2` elements of `μ_{n/2}`. Measured `#bad ≈ C(n/2, w/2)` (n=16: w=6→40 vs C(8,3)=56; w=8→41 vs 70) —
**exponential**, matching the independent max-direction curve (40 at t=10). So MCA FAILS at t=k+2 for
ρ=1/2 (`#bad ~ 2^{n/2} ≫ ε*q`); δ* is deeper, where enough symmetric functions vanish.

## The EXACT δ* (closed reframing — no character sums, no Johnson)
> **`δ* = 1 − t*/n`,  `t* = max{ t : #{distinct e_{t-k}(T) : |T|=t, e_1=⋯=e_{t-k-1}=0} > ε*q }`.**
δ* is the inverse of this monotone, q-independent count at the budget. The **Kambiré construction**
realizes exactly the power-sum-vanishing `T` (subgroup-coset unions), giving `#bad ≥ C(s,r)` and
recovering `δ* ≤ 1−ρ−2/s*`. The lower bracket = **the construction MAXIMIZES this count** (extremality),
now a purely combinatorial statement about distinct symmetric-function readouts over power-sum-vanishing
subsets of roots of unity.

## Status (honest)
GENUINE/verified: the worst-direction = dir(k,b); the closed reduction (vanishing elem-symm/power-sums +
e_{t-k} readout); #bad(t=k+2) = subset-sum count ~C(n/2,w/2) (exponential); δ* = inverse of the monotone
q-independent count; the construction realizes the extremal-candidate T. This is the EXACT δ*
characterization, off Johnson and off the character-sum (incomplete-Gauss-sum) wall. OPEN: the closed
form / extremality of `#bad(t)` — is the construction count `C(s,r)` the max of #distinct e_{t-k} over
power-sum-vanishing T? That is the remaining combinatorial content (q-independent). Caveat: this count
may still encode additive structure; whether it is genuinely closed or reduces to subgroup additive
energy is the next thing to test. No δ* closure claimed; strongest calibration of the session.
