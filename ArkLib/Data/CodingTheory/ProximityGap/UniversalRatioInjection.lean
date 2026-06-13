/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StronglyFarSubsetLaw

/-!
# The universal ratio injection (#371): the radius-free MCA ceiling

The strongly-far hypothesis is removable.  For EVERY stack `(u₀, u₁)` — far,
near-code, or codeword — and EVERY radius `δ`, each bad scalar is a subset ratio
of a `(k+1)`-subset with nonvanishing direction residual, exclusively:

  **`badSet(u₀, u₁, δ) ⊆ {−e_T(u₀)/e_T(u₁) : e_T(u₁) ≠ 0}`**.

The dichotomy on a witness `S`: any `(k+1)`-subset of `S` with `e_T(u₁) ≠ 0`
pins the scalar through the line equation; if NO such subset exists, the
**gluing lemma** (`exists_codeword_agreeOn_of_canon_residuals`) produces a single
codeword matching `u₁` on all of `S` — and the line equation then forces the same
for `u₀` — yielding a joint pair that contradicts the event's last clause.
(Witnesses smaller than `k+1` always carry a joint Lagrange pair.)

Consequences, all radius-free and unconditional:

* **The universal ceiling** (`universal_badScalars_card_le_choose`,
  `universal_epsMCA_le_choose_div`): `#bad ≤ C(n, k+1)` and
  `ε_mca(RS_k, δ) ≤ C(n, k+1)/q` at EVERY radius `δ` — through the window, to
  capacity.  Attained at the boundary slice (`BoundaryFarPin12289.lean`:
  `56 = C(8,3)` exactly), so the constant is sharp.  (At fixed `k` this is the
  MCA analogue, strengthened from the equal-threshold CA case, of Round-17's
  `bad_card_le_choose` = ePrint 2026/858 Thm 7; at production dimension
  `k = Θ(ρn)` the binomial is exponential — the prize window stays open.)

* **The agreement-indexed ceiling** (`badScalars_card_le_choose_sub_agree`):
  for ANY codeword `c`,  `#bad ≤ C(n, k+1) − C(|agree(c, u₁)|, k+1)` —
  subsets inside an agreement set have vanishing residual, so they never own a
  scalar.  Probe-exact at every measured distance (`probe_far_subset_law.py` P3:
  near-code classes cap at `C(8,3) − C(8−s,3)` = 21, 36, 46, 52, 55 for
  `s = 1..5`): far directions are the strict extremizers of the boundary slice,
  inverting the near-tube intuition.

* **The codeword-direction zero law** (`badScalars_eq_zero_of_mem`): directions
  IN the code have no bad scalars at any radius — WB-3b, radius-free.

Probe: `scripts/probes/probe_far_subset_law.py` — the candidate(=ratio) method
matches the faithful `mcaEvent` enumeration exactly (0 mismatches, 50 stacks),
and the global boundary extremizer search never beats `C(n, k+1)`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The generic enumeration of a sized subset -/

/-- The canonical (monotone) enumeration of a subset of any known size. -/
noncomputable def enumTuple {m : ℕ} (T : Finset (Fin n)) (h : T.card = m) :
    Fin m → Fin n := fun a => ((T.orderIsoOfFin h) a : Fin n)

theorem enumTuple_injective {m : ℕ} (T : Finset (Fin n)) (h : T.card = m) :
    Function.Injective (enumTuple T h) := fun a b hab =>
  (T.orderIsoOfFin h).injective (Subtype.ext hab)

theorem enumTuple_mem {m : ℕ} (T : Finset (Fin n)) (h : T.card = m)
    (a : Fin m) : enumTuple T h a ∈ T := ((T.orderIsoOfFin h) a).2

/-! ## The gluing lemma -/

open Classical in
/-- **The gluing lemma**: if the word's residual vanishes on the canonical tuple
of EVERY `(k+1)`-subset of `S`, then a single codeword matches the word on all of
`S`.  (Two interpolants on overlapping `(k+1)`-subsets agree on their `k` shared
points, hence are equal.) -/
theorem exists_codeword_agreeOn_of_canon_residuals (dom : Fin n ↪ F) {k : ℕ}
    {S : Finset (Fin n)} {v : Fin n → F}
    (hres : ∀ T ⊆ S, ∀ h : T.card = k + 1,
      residual dom k (canonTuple T h) v = 0) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ S, c i = v i := by
  by_cases hSk : S.card ≤ k
  · exact exists_codeword_agreeOn_of_card_le dom hSk v
  push_neg at hSk
  obtain ⟨T₀, hT₀S, hT₀card⟩ := Finset.exists_subset_card_eq hSk
  obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom _
    (canonTuple_injective T₀ hT₀card) (hres T₀ hT₀S hT₀card)
  refine ⟨c, hcC, fun x hx => ?_⟩
  by_cases hxT₀ : x ∈ T₀
  · obtain ⟨a, ha⟩ := canonTuple_surjOn T₀ hT₀card hxT₀
    rw [← ha]
    exact hcag a
  · have hT₀ne : T₀.Nonempty := by
      rw [← Finset.card_pos, hT₀card]
      omega
    obtain ⟨p₀, hp₀⟩ := hT₀ne
    have hKcard : (T₀.erase p₀).card = k := by
      rw [Finset.card_erase_of_mem hp₀, hT₀card]
      omega
    have hxK : x ∉ T₀.erase p₀ := fun hxK => hxT₀ (Finset.erase_subset _ _ hxK)
    have hTxcard : (insert x (T₀.erase p₀)).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hxK, hKcard]
    have hTxS : insert x (T₀.erase p₀) ⊆ S := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyK
      · exact hx
      · exact hT₀S (Finset.erase_subset _ _ hyK)
    obtain ⟨c', hc'C, hc'ag⟩ := extension_of_residual_eq_zero dom _
      (canonTuple_injective _ hTxcard) (hres _ hTxS hTxcard)
    have hcc' : c = c' := by
      refine codeword_eq_of_common_tuple dom (y := v) hcC hc'C
        (enumTuple (T₀.erase p₀) hKcard)
        (enumTuple_injective (T₀.erase p₀) hKcard) ?_ ?_
      · intro a
        have hmem : enumTuple (T₀.erase p₀) hKcard a ∈ T₀ :=
          Finset.erase_subset _ _ (enumTuple_mem (T₀.erase p₀) hKcard a)
        obtain ⟨b, hb⟩ := canonTuple_surjOn T₀ hT₀card hmem
        rw [← hb]
        exact hcag b
      · intro a
        have hmem : enumTuple (T₀.erase p₀) hKcard a ∈ insert x (T₀.erase p₀) :=
          Finset.mem_insert_of_mem (enumTuple_mem (T₀.erase p₀) hKcard a)
        obtain ⟨b, hb⟩ := canonTuple_surjOn _ hTxcard hmem
        rw [← hb]
        exact hc'ag b
    have hxTx : x ∈ insert x (T₀.erase p₀) := Finset.mem_insert_self _ _
    obtain ⟨b, hb⟩ := canonTuple_surjOn _ hTxcard hxTx
    rw [hcc', ← hb]
    exact hc'ag b

/-! ## The nonvanishing ratio set -/

open Classical in
/-- The nonvanishing ratio set: subset ratios over the `(k+1)`-subsets whose
direction residual does not vanish. -/
noncomputable def ratioSetNZ (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    Finset F :=
  (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach.filter fun T =>
      residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁
        ≠ 0).image fun T =>
    -(residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₀)
      / residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁

open Classical in
theorem ratioSetNZ_card_le (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    (ratioSetNZ dom k u₀ u₁).card ≤ n.choose (k + 1) := by
  refine le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) ?_)
  rw [Finset.card_attach, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-! ## The universal injection -/

open Classical in
/-- **THE UNIVERSAL RATIO INJECTION** — every direction, every radius: each bad
scalar is the ratio of a `(k+1)`-subset with nonvanishing direction residual.
The dichotomy: a witness either carries such a subset (which pins the scalar), or
all its subsets glue into a joint codeword pair, contradicting the event. -/
theorem bad_subset_ratioSetNZ (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      ⊆ ratioSetNZ dom k u₀ u₁ := by
  intro γ hγ
  obtain ⟨S, hSsz, ⟨wcd, hwC, hag⟩, hnj⟩ := (Finset.mem_filter.mp hγ).2
  have hSk : k + 1 ≤ S.card := by
    by_contra hlt
    push_neg at hlt
    have hSle : S.card ≤ k := by omega
    obtain ⟨v₀, hv₀C, hv₀⟩ := exists_codeword_agreeOn_of_card_le dom hSle u₀
    obtain ⟨v₁, hv₁C, hv₁⟩ := exists_codeword_agreeOn_of_card_le dom hSle u₁
    exact hnj ⟨v₀, hv₀C, v₁, hv₁C, fun i hi => ⟨hv₀ i hi, hv₁ i hi⟩⟩
  obtain ⟨P, hPdeg, rfl⟩ := hwC
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hline0 : ∀ T, T ⊆ S → ∀ h : T.card = k + 1,
      residual dom k (canonTuple T h) u₀
        + γ * residual dom k (canonTuple T h) u₁ = 0 := by
    intro T hTS h
    rw [← residual_line]
    refine residual_eq_zero_of_extends dom k _ hPdeg' fun a => ?_
    have hmem : canonTuple T h a ∈ S := hTS (canonTuple_mem T h a)
    have := hag (canonTuple T h a) hmem
    simpa [smul_eq_mul] using this.symm
  by_cases hA : ∃ T, T ⊆ S ∧ ∃ h : T.card = k + 1,
      residual dom k (canonTuple T h) u₁ ≠ 0
  · obtain ⟨T, hTS, h, h1⟩ := hA
    rw [ratioSetNZ, Finset.mem_image]
    refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_attach _ _, h1⟩
    · exact (gamma_eq_of_owned dom k _ h1 (hline0 T hTS h)).symm
  · push_neg at hA
    exfalso
    apply hnj
    have hres1 : ∀ T ⊆ S, ∀ h : T.card = k + 1,
        residual dom k (canonTuple T h) u₁ = 0 := fun T hTS h => hA T hTS h
    have hres0 : ∀ T ⊆ S, ∀ h : T.card = k + 1,
        residual dom k (canonTuple T h) u₀ = 0 := by
      intro T hTS h
      have hl := hline0 T hTS h
      rw [hres1 T hTS h] at hl
      simpa using hl
    obtain ⟨v₀, hv₀C, hv₀⟩ :=
      exists_codeword_agreeOn_of_canon_residuals dom hres0
    obtain ⟨v₁, hv₁C, hv₁⟩ :=
      exists_codeword_agreeOn_of_canon_residuals dom hres1
    exact ⟨v₀, hv₀C, v₁, hv₁C, fun i hi => ⟨hv₀ i hi, hv₁ i hi⟩⟩

/-! ## The universal ceiling -/

open Classical in
/-- **The universal count**: `#bad ≤ C(n, k+1)` for every stack at every radius. -/
theorem universal_badScalars_card_le_choose (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n.choose (k + 1) :=
  le_trans (Finset.card_le_card (bad_subset_ratioSetNZ dom hk u₀ u₁))
    (ratioSetNZ_card_le dom k u₀ u₁)

open Classical in
/-- **THE RADIUS-FREE MCA CEILING**: `ε_mca(RS_k, δ) ≤ C(n, k+1)/q` at EVERY
radius — through the window, to capacity, unconditionally.  Sharp: attained at
the boundary slice (`BoundaryFarPin12289`). -/
theorem universal_epsMCA_le_choose_div (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast universal_badScalars_card_le_choose dom hk (u 0) (u 1)

/-! ## The agreement-indexed refinement -/

open Classical in
/-- Subsets inside a codeword's agreement set have vanishing direction residual,
so they never own a scalar: the nonvanishing ratio set loses one subset per
`(k+1)`-subset of the agreement set. -/
theorem ratioSetNZ_card_le_choose_sub (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (u₀ : Fin n → F) {u₁ : Fin n → F} {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (ratioSetNZ dom k u₀ u₁).card
      ≤ n.choose (k + 1) - ((agreeSet c u₁).card).choose (k + 1) := by
  classical
  -- subsets of the agreement set have vanishing direction residual
  have hvanish : ∀ T : {T // T ∈ (Finset.univ : Finset (Fin n)).powersetCard
      (k + 1)}, T.1 ⊆ agreeSet c u₁ →
      residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁
        = 0 := by
    intro T hTagr
    obtain ⟨Q, hQdeg, rfl⟩ := hc
    have hQdeg' : Q.natDegree < k := by
      by_cases hQ0 : Q = 0
      · subst hQ0
        simpa using hk
      · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQdeg
    refine residual_eq_zero_of_extends dom k _ hQdeg' fun a => ?_
    have hmem := hTagr (canonTuple_mem T.1 (Finset.mem_powersetCard.mp T.2).2 a)
    rw [agreeSet, Finset.mem_filter] at hmem
    exact hmem.2.symm
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach)
    (p := fun T => residual dom k
      (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁ ≠ 0)
  have hAcard : ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach.card
      = n.choose (k + 1) := by
    rw [Finset.card_attach, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin]
  rw [hAcard] at hsplit
  -- the agreement subsets inject into the vanishing class
  have hagrcount : ((agreeSet c u₁).card).choose (k + 1)
      ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach).filter
          (fun T => ¬ residual dom k
            (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁ ≠ 0)).card := by
    calc ((agreeSet c u₁).card).choose (k + 1)
        = ((agreeSet c u₁).powersetCard (k + 1)).attach.card := by
          rw [Finset.card_attach, Finset.card_powersetCard]
      _ ≤ _ := by
          refine Finset.card_le_card_of_injOn (fun U =>
            ⟨U.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
              (Finset.mem_powersetCard.mp U.2).2⟩⟩) ?_ ?_
          · intro U hU
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_attach _ _, ?_⟩
            exact not_not_intro
              (hvanish _ (Finset.mem_powersetCard.mp U.2).1)
          · intro U hU U' hU' heq
            have h1 : U.1 = U'.1 := by
              have := congrArg Subtype.val heq
              simpa using this
            exact Subtype.ext h1
  have hfil : (ratioSetNZ dom k u₀ u₁).card
      ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach).filter
          (fun T => residual dom k
            (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁ ≠ 0)).card := by
    rw [ratioSetNZ]
    exact Finset.card_image_le
  omega

open Classical in
/-- **THE AGREEMENT-INDEXED CEILING** — every stack, every radius, any codeword:
`#bad ≤ C(n, k+1) − C(a, k+1)` where `a` is the codeword's agreement with `u₁`.
Far directions (`a ≤ k`) get the full ceiling — and attain it; near directions
lose exactly the agreement block (probe-exact at every measured distance);
codeword directions get zero. -/
theorem badScalars_card_le_choose_sub_agree (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (u₀ : Fin n → F) {u₁ : Fin n → F} {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n.choose (k + 1) - ((agreeSet c u₁).card).choose (k + 1) :=
  le_trans (Finset.card_le_card (bad_subset_ratioSetNZ dom hk u₀ u₁))
    (ratioSetNZ_card_le_choose_sub dom hk u₀ hc)

open Classical in
/-- **The codeword-direction zero law (WB-3b, radius-free)**: a direction IN the
code has NO bad scalars at any radius. -/
theorem badScalars_eq_zero_of_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (u₀ : Fin n → F) {u₁ : Fin n → F}
    (hu₁ : u₁ ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      = 0 := by
  have h := badScalars_card_le_choose_sub_agree dom hk (δ := δ) u₀
    (u₁ := u₁) hu₁
  have hagr : agreeSet u₁ u₁ = Finset.univ := by
    rw [agreeSet]
    simp
  rw [hagr, Finset.card_univ, Fintype.card_fin] at h
  omega

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.exists_codeword_agreeOn_of_canon_residuals
#print axioms ProximityGap.Ownership.bad_subset_ratioSetNZ
#print axioms ProximityGap.Ownership.universal_badScalars_card_le_choose
#print axioms ProximityGap.Ownership.universal_epsMCA_le_choose_div
#print axioms ProximityGap.Ownership.ratioSetNZ_card_le_choose_sub
#print axioms ProximityGap.Ownership.badScalars_card_le_choose_sub_agree
#print axioms ProximityGap.Ownership.badScalars_eq_zero_of_mem
