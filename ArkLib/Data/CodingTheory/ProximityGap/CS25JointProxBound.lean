/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallEntropy
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# Counting jointly-close stacks (toward T4.17, #82)

The `#{jointProx}` upper bound — ingredient (b) of the CS25 complete-CA-breakdown count budget
`hfar` — proved here end to end. A stack is jointly `δ`-close to `C` iff its interleaving
`⋈|u = uᵀ` is within `δ` of *some* interleaved codeword; the interleaved code
`C^⋈κ = {V | ∀ k, V.transpose k ∈ C}` is the `κ`-fold product of `C` (transpose bijection), with
`|C|^|κ|` codewords. The union bound over those codewords then gives, in successively explicit
forms:

* `card_jointProximity_le`      : `#{jointProx} ≤ |C|^|κ| · V'_{⌊δn⌋}`;
* `card_jointProximity_le_volume`: `… = |C|^|κ| · hammingBallVolume(q^|κ|, δ, n)`;
* `card_jointProximity_le_qEntropy`: `… ≤ |C|^|κ| · (n+1) · (q^|κ|)^{n·H_{q^|κ|}(δ)}` (below the
  `q^|κ|`-ary capacity).

## Band analysis: why this does **not** close T4.17 by averaging

`rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts` discharges T4.17 from the count budget
`hsum : q^{n+1}·#{far} + #{jointProx} < q^{2n}` (using `sum_far_card_eq`). With coverage saturated
(`#{far} ≈ 0` from `hδ_lo`), `hsum` reduces to `#{jointProx} < q^{2n}`, i.e. `H_{q²}(δ) < 1 − ρ`
(`ρ = k/n`, `κ = Fin 2`). The bound above is essentially **tight** (the union bound is the right
upper bound on a covered set), so this is the genuine obstruction, not slack:

* At high rate (`ρ` near `hδ_hi`'s ceiling `1 − δ − 2/n`) the *interleaved* code `C^⋈` has rate
  `2ρ ≈ 2(1−δ)`, far above its own capacity, so its `δ`-coverage **saturates**:
  `#{jointProx} ≈ q^{2n}` and `hsum` is simply **false** — almost every stack is jointly close.
* The breakdown `ε_ca = 1` is nonetheless true there, witnessed by a *rare* covered,
  not-jointly-close stack that the averaging/counting budget provably cannot locate.

Hence T4.17's full-band closure requires the **explicit entropy-ball construction** of that witness
(`rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_covered_stack` with a *named* covered stack),
not the counting route — placing it in the same explicit-construction class as T4.16/T4.18. The
counting route does suffice on the sub-band where `H_{q²}(δ) < 1 − ρ` (interleaved coverage below
saturation), for which the lemmas here are exactly the input.
-/

open Code
open scoped NNReal

namespace CS25

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The interleaved code is the `κ`-fold product of `C`.** As a type, `C^⋈κ ≃ (κ → C)` via the
transpose map `V ↦ (k ↦ Vᵀ k)`. -/
def interleavedCodeSetEquiv (C : Set (ι → A)) :
    ↥(interleavedCodeSet (κ := κ) C) ≃ (κ → ↥C) where
  toFun := fun V k => ⟨V.1.transpose k, V.2 k⟩
  invFun := fun g => ⟨Matrix.of (fun i k => (g k).1 i), fun k => (g k).2⟩
  left_inv := fun V => by ext i k; rfl
  right_inv := fun g => by ext k i; rfl

/-- **The interleaved code `C^⋈κ` has `|C|^|κ|` codewords.** -/
theorem interleavedCodeSet_card (C : Set (ι → A)) [Fintype ↥C]
    [Fintype ↥(interleavedCodeSet (κ := κ) C)] :
    Fintype.card ↥(interleavedCodeSet (κ := κ) C) = (Fintype.card ↥C) ^ (Fintype.card κ) := by
  rw [Fintype.card_congr (interleavedCodeSetEquiv (κ := κ) C), Fintype.card_fun]

/-- **Union (covering) upper bound.** For any finite code `𝒞`, the number of words within Hamming
distance `r` of `𝒞` is at most `|𝒞| · V` (the union bound). Derived from the first moment
`ArkLib.CS25.sum_closeCount_eq`: each covered word has `closeCount ≥ 1`. -/
theorem card_close_le_card_mul_vol {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]
    (𝒞 : Finset (ι → F)) (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F => ArkLib.CS25.closeCount 𝒞 r w ≠ 0)).card
      ≤ 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
  classical
  calc (Finset.univ.filter (fun w : ι → F => ArkLib.CS25.closeCount 𝒞 r w ≠ 0)).card
      = ∑ w : ι → F, (if ArkLib.CS25.closeCount 𝒞 r w ≠ 0 then 1 else 0) := by
        rw [Finset.card_filter]
    _ ≤ ∑ w : ι → F, ArkLib.CS25.closeCount 𝒞 r w := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        by_cases h : ArkLib.CS25.closeCount 𝒞 r w ≠ 0
        · rw [if_pos h]; omega
        · rw [if_neg h]; exact Nat.zero_le _
    _ = 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card :=
        ArkLib.CS25.sum_closeCount_eq 𝒞 r

open Classical in
/-- **Jointly-`e`-close stack count bound.** A stack `u` is jointly `e`-close to `C` iff its
interleaving `⋈|u = uᵀ` is within Hamming distance `e` of some interleaved codeword. By the union
bound over the interleaved code `C^⋈κ` (`|C|^|κ|` codewords), the number of jointly-`e`-close stacks
is at most `|C|^|κ| · V'`, where `V'` is the interleaved-ball volume. -/
theorem card_jointProximityNat_le (C : Set (ι → A)) [AddCommGroup A] [Fintype ↥C] (e : ℕ) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximityNat C (u := u) e)).card
      ≤ (Fintype.card ↥C) ^ (Fintype.card κ)
        * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card := by
  classical
  -- the interleaved code, as the image Finset of its codeword subtype (avoids `Set.toFinset`)
  set 𝒞 : Finset (InterleavedWord A κ ι) :=
    Finset.univ.image (fun v : ↥(interleavedCodeSet (κ := κ) C) => v.val) with h𝒞
  have hiff : ∀ u : WordStack A κ ι,
      jointProximityNat C (u := u) e ↔ ArkLib.CS25.closeCount 𝒞 e u.transpose ≠ 0 := by
    intro u
    rw [jointProximityNat_iff_closeToInterleavedCodeword, ArkLib.CS25.closeCount,
      Finset.card_ne_zero, Finset.filter_nonempty_iff]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.val, Finset.mem_image_of_mem _ (Finset.mem_univ v), hv⟩
    · rintro ⟨c, hcS, hc⟩
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hcS
      exact ⟨v, hc⟩
  have hreindex :
      (Finset.univ.filter (fun u : WordStack A κ ι => jointProximityNat C (u := u) e)).card
        = (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            ArkLib.CS25.closeCount 𝒞 e w ≠ 0)).card := by
    refine Finset.card_nbij' (fun u => u.transpose) (fun w => w.transpose) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact (hiff u).mp hu
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [hiff]; simpa [Matrix.transpose_transpose] using hw
    · intro u _; simp [Matrix.transpose_transpose]
    · intro w _; simp [Matrix.transpose_transpose]
  rw [hreindex]
  calc (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            ArkLib.CS25.closeCount 𝒞 e w ≠ 0)).card
      ≤ 𝒞.card
          * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card :=
        card_close_le_card_mul_vol _ e
    _ = (Fintype.card ↥C) ^ (Fintype.card κ)
          * (Finset.univ.filter (fun w : InterleavedWord A κ ι => hammingDist w 0 ≤ e)).card := by
        rw [h𝒞, Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
          interleavedCodeSet_card]

/-- **Bridge.** Relative joint proximity at `δ` is absolute joint proximity at `⌊δ·n⌋`. Immediate
from `Code.relDistFromCode_le_iff_distFromCode_le` (`δᵣ ≤ δ ↔ Δ₀ ≤ ⌊δ·n⌋`). -/
theorem jointProximity_iff_jointProximityNat [Nonempty ι] (C : Set (ι → A))
    (u : WordStack A κ ι) (δ : ℝ≥0) :
    jointProximity C (u := u) δ ↔
      jointProximityNat C (u := u) ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  unfold jointProximity jointProximityNat
  exact Code.relDistFromCode_le_iff_distFromCode_le _ δ

open Classical in
/-- **Jointly-`δ`-close stack count bound (relative form).** The number of stacks jointly within
relative distance `δ` of `C` is at most `|C|^|κ| · V'`, where `V'` is the interleaved-ball volume at
radius `⌊δ·n⌋`. This is ingredient (b) of the CS25 complete-CA-breakdown count budget `hfar`. -/
theorem card_jointProximity_le [Nonempty ι] (C : Set (ι → A)) [AddCommGroup A] [Fintype ↥C]
    (δ : ℝ≥0) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card
      ≤ (Fintype.card ↥C) ^ (Fintype.card κ)
        * (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
            hammingDist w 0 ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)).card := by
  have hset :
      (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ))
        = (Finset.univ.filter (fun u : WordStack A κ ι =>
            jointProximityNat C (u := u) ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact jointProximity_iff_jointProximityNat C u δ
  rw [hset]
  exact card_jointProximityNat_le C _

/-- NNReal/Real agreement of the ball radius floor `⌊δ·n⌋`. -/
private theorem floor_nnreal_eq_real (δ : ℝ≥0) (n : ℕ) :
    ⌊δ * (n : ℝ≥0)⌋₊ = ⌊(δ : ℝ) * (n : ℝ)⌋₊ := by
  have hcoe : ((δ * (n : ℝ≥0) : ℝ≥0) : ℝ) = (δ : ℝ) * (n : ℝ) := by push_cast; ring
  refine le_antisymm (Nat.le_floor ?_) (Nat.le_floor ?_)
  · calc ((⌊δ * (n : ℝ≥0)⌋₊ : ℝ))
        = ((⌊δ * (n : ℝ≥0)⌋₊ : ℝ≥0) : ℝ) := by push_cast; ring
      _ ≤ ((δ * (n : ℝ≥0) : ℝ≥0) : ℝ) := by exact_mod_cast Nat.floor_le (zero_le _)
      _ = (δ : ℝ) * (n : ℝ) := hcoe
  · have h : ((⌊(δ : ℝ) * (n : ℝ)⌋₊ : ℝ)) ≤ ((δ * (n : ℝ≥0) : ℝ≥0) : ℝ) := by
      rw [hcoe]; exact Nat.floor_le (by positivity)
    exact_mod_cast h

/-- The interleaved-ball volume `V'_{⌊δn⌋}` equals `hammingBallVolume (q^|κ|) δ n`, the explicit
sum `∑_{i≤⌊δn⌋} C(n,i)(q^|κ|-1)^i` over the interleaved alphabet `κ→A`. -/
theorem interleaved_ball_card_eq_volume [Nonempty ι] [AddCommGroup A] (δ : ℝ≥0) :
    (Finset.univ.filter (fun w : InterleavedWord A κ ι =>
        hammingDist w 0 ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)).card
      = CodingTheory.hammingBallVolume (Fintype.card (κ → A)) (δ : ℝ) (Fintype.card ι) := by
  have heq := floor_nnreal_eq_real δ (Fintype.card ι)
  rw [CodingTheory.hammingBallVolume_eq_ncard_hammingBall (δ : ℝ) (0 : ι → (κ → A)),
    ← CodingTheory.filter_card_eq_hammingBall_ncard, ← heq]
  refine Finset.card_nbij' id id ?_ ?_ ?_ ?_ <;> intro w hw <;>
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, id_eq,
      hammingDist_comm] at hw ⊢ <;> exact hw

open Classical in
/-- **Explicit (band-ready) `#{jointProx}` bound.** `#{u : jointProximity C u δ} ≤
|C|^|κ| · hammingBallVolume(q^|κ|, δ, n)` — ingredient (b) of the CS25 breakdown budget `hfar`, with
the interleaved-ball volume in explicit summation form (to be bounded by
`hammingBallVolume_le_qEntropy_real_radius` in the final band arithmetic). -/
theorem card_jointProximity_le_volume [Nonempty ι] (C : Set (ι → A)) [AddCommGroup A]
    [Fintype ↥C] (δ : ℝ≥0) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card
      ≤ (Fintype.card ↥C) ^ (Fintype.card κ)
        * CodingTheory.hammingBallVolume (Fintype.card (κ → A)) (δ : ℝ) (Fintype.card ι) := by
  refine le_trans (card_jointProximity_le C δ) (Nat.mul_le_mul_left _ ?_)
  exact le_of_eq (interleaved_ball_card_eq_volume δ)

open Classical in
/-- **Explicit qEntropy `#{jointProx}` bound.** Below the `q^|κ|`-ary capacity
(`δ ≤ 1 − 1/q^|κ|`), the jointly-`δ`-close stack count obeys
`#{jointProx} ≤ |C|^|κ| · (n+1) · (q^|κ|)^{n · H_{q^|κ|}(δ)}`. This is ingredient (b) of the CS25
breakdown budget `hfar` in the exponential entropy form the final band inequality consumes (the
`q^{2k}·(n+1)·q^{2n·H_{q²}(δ)}` term for the `Fin 2` stacks). -/
theorem card_jointProximity_le_qEntropy [Nonempty ι] (C : Set (ι → A)) [AddCommGroup A]
    [Fintype ↥C] (δ : ℝ≥0)
    (hq : 2 ≤ Fintype.card (κ → A))
    (hδcap : (δ : ℝ) ≤ 1 - 1 / (Fintype.card (κ → A) : ℝ)) :
    ((Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card : ℝ)
      ≤ ((Fintype.card ↥C) ^ (Fintype.card κ) : ℝ)
        * (((Fintype.card ι : ℝ) + 1)
          * (Fintype.card (κ → A) : ℝ)
              ^ ((Fintype.card ι : ℝ) * CodingTheory.qEntropy (Fintype.card (κ → A)) (δ : ℝ))) := by
  have hvol : ((Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card : ℝ)
      ≤ ((Fintype.card ↥C) ^ (Fintype.card κ) : ℝ)
        * (CodingTheory.hammingBallVolume (Fintype.card (κ → A)) (δ : ℝ) (Fintype.card ι) : ℝ) := by
    have h := card_jointProximity_le_volume (κ := κ) C δ
    calc ((Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card : ℝ)
        ≤ (((Fintype.card ↥C) ^ (Fintype.card κ)
            * CodingTheory.hammingBallVolume (Fintype.card (κ → A)) (δ : ℝ) (Fintype.card ι) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = _ := by push_cast; ring
  refine hvol.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact CodingTheory.hammingBallVolume_le_qEntropy_real_radius hq (δ : ℝ)
    Fintype.card_pos δ.coe_nonneg hδcap

/-- **Real-analysis core of the sub-band jointProx inequality.** For `Q > 1`, the explicit qEntropy
`#{jointProx}` bound `Q^k · (n+1) · Q^{n·H}` drops below `Q^n` exactly when the rate-plus-entropy
budget `k + log_Q(n+1) + n·H ≤ n` holds — i.e. the sub-band condition `ρ + H_Q(δ) < 1` (with the
`log_Q(n+1)/n` slack). Pure `rpow`/`logb` arithmetic; the `Fin 2` instance has `Q = q²`,
`Q^k = q^{2k} = |C|^|κ|`, `Q^n = #stacks`. -/
theorem pow_succ_rpow_entropy_le {Q : ℝ} (hQ : 1 < Q) (k n : ℕ) (H : ℝ)
    (h : (k : ℝ) + Real.logb Q ((n : ℝ) + 1) + (n : ℝ) * H ≤ (n : ℝ)) :
    Q ^ (k : ℝ) * (((n : ℝ) + 1) * Q ^ ((n : ℝ) * H)) ≤ Q ^ (n : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogb : ((n : ℝ) + 1) = Q ^ Real.logb Q ((n : ℝ) + 1) :=
    (Real.rpow_logb hQ0 hQ.ne' hn1).symm
  calc Q ^ (k : ℝ) * (((n : ℝ) + 1) * Q ^ ((n : ℝ) * H))
      = Q ^ (k : ℝ) * (Q ^ Real.logb Q ((n : ℝ) + 1) * Q ^ ((n : ℝ) * H)) := by rw [← hlogb]
    _ = Q ^ ((k : ℝ) + (Real.logb Q ((n : ℝ) + 1) + (n : ℝ) * H)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ Q ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)

/-- **`#stacks = Q^n`** for the interleaved alphabet `Q = |κ→A|`, `n = |ι|`. -/
theorem card_wordStack_eq :
    Fintype.card (WordStack A κ ι) = (Fintype.card (κ → A)) ^ (Fintype.card ι) := by
  show Fintype.card (κ → ι → A) = (Fintype.card (κ → A)) ^ Fintype.card ι
  simp only [Fintype.card_fun]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

open Classical in
/-- **JointProx half of the band inequality, closed on the sub-band.** When the code's rate
identity `|C|^|κ| = Q^k` holds (e.g. RS, `|C| = q^k`, `Q = q^|κ|`) and the sub-band rate condition
`k + log_Q(n+1) + n·H_Q(δ) ≤ n` holds below capacity, the jointly-`δ`-close stacks number at most the
total stack count: `#{jointProx} ≤ #stacks`. Combines `card_jointProximity_le_qEntropy` with the
`rpow` core `pow_succ_rpow_entropy_le`. -/
theorem card_jointProximity_le_card_stacks_of_subband [Nonempty ι] (C : Set (ι → A))
    [AddCommGroup A] [Fintype ↥C] (δ : ℝ≥0) (k : ℕ)
    (hq : 2 ≤ Fintype.card (κ → A))
    (hδcap : (δ : ℝ) ≤ 1 - 1 / (Fintype.card (κ → A) : ℝ))
    (hrate : (Fintype.card ↥C) ^ (Fintype.card κ) = (Fintype.card (κ → A)) ^ k)
    (hsub : (k : ℝ) + Real.logb (Fintype.card (κ → A)) ((Fintype.card ι : ℝ) + 1)
        + (Fintype.card ι : ℝ) * CodingTheory.qEntropy (Fintype.card (κ → A)) (δ : ℝ)
          ≤ (Fintype.card ι : ℝ)) :
    (Finset.univ.filter (fun u : WordStack A κ ι => jointProximity C (u := u) δ)).card
      ≤ Fintype.card (WordStack A κ ι) := by
  have hQ1 : (1 : ℝ) < (Fintype.card (κ → A) : ℝ) := by exact_mod_cast hq
  rw [← Nat.cast_le (α := ℝ), card_wordStack_eq, Nat.cast_pow,
    ← Real.rpow_natCast (Fintype.card (κ → A) : ℝ) (Fintype.card ι)]
  refine (card_jointProximity_le_qEntropy (κ := κ) C δ hq hδcap).trans ?_
  have hcard : (((Fintype.card ↥C) ^ (Fintype.card κ) : ℕ) : ℝ)
      = (Fintype.card (κ → A) : ℝ) ^ (k : ℝ) := by
    rw [hrate, Nat.cast_pow, Real.rpow_natCast]
  rw [hcard]
  exact pow_succ_rpow_entropy_le hQ1 k (Fintype.card ι) _ hsub

end CS25
