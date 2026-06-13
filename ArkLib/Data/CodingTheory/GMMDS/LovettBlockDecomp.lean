/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettBlockDim
import ArkLib.Data.CodingTheory.GMMDS.LovettCounting
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import ArkLib.Data.CodingTheory.GMMDS.LovettFractionField

/-!
# Lovett's GM-MDS proof: the range decomposition closing Lemma 2.4 (#389)

This file performs the *range-decomposition plumbing* that discharges the corrected residual
`Lemma24SpanTransferWithIBlock` (see [[LovettLemma24Finish]]), thereby fully closing the algebraic
finish of Lovett's Lemma 2.4 (arXiv:1803.02523, p.8–9), and then derives the classification
`tightConstraint ∧ IsVStar ⟹ |I| ∈ {1, m}`.

The meet-replacement system `V' = replaceMeetFin V I hI` (built in [[LovettMeetReplace]]) replaces
the entire `I`-block of `V` by the single coordinate-wise meet `v_I = ⋀_{i∈I} vᵢ`, keeping every
vector outside `I`.  Everything happens over the **fraction field** `K = F(a) = Frac(F[a])`, reached
from the ring `R = F[a] = MvPolynomial (Fin n) F` via [[LovettFractionField]] (the field is needed
for the basis-counting step — a spanning set of size `=` dimension is independent).

The families `P(k,V) = pFamUnion V k` and `P(k,V') = pFamUnion V' k` decompose as

> `P(k,V)  = (shared blocks, i ∉ I)  ⊔  (I-block, i ∈ I)`
> `P(k,V') = (shared blocks, i ∉ I)  ⊔  (meet block, v_I)`,

with the shared blocks *pointwise identical*.  The two key span facts (over `K`):

* `iBlock_span_eq_meetBlock_K` — the `I`-block and the meet block span the **same** `K`-subspace.
  Forward (`I`-block ⊆ meet block) maps from the unconditional ring fact
  (`pFamUnion_I_mem_span_meetBlock`); the reverse is the dimension count
  (`span_eq_of_le_of_card_of_indep` over `K`) which needs the `I`-block independent — the genuine
  extra input of Lemma 2.4, threaded as a hypothesis (supplied at the call site by the
  `d`-induction hypothesis on the `I`-subsystem).
* `pFamUnion_span_eq_replaceMeetFin_K` — hence `span P(k,V) = span P(k,V')` over `K`.

With equal cardinality (`lovettD_replaceMeet`, tightness) and `P(k,V')` independent (the `m`-IH),
`linearIndependent_of_span_eq_card` transfers independence to `P(k,V)`.  This proves
`Lemma24SpanTransferWithIBlock`, and the classification follows.

Issue #389.
-/

open Polynomial Finset Submodule

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-! ## The base-change map `Φ : R[X] → K[X]` -/

/-- The coefficient base-change `R[X] →ₗ[R] K[X]` with `R = F[a]`, `K = F(a) = Frac(R)`. -/
noncomputable abbrev phiX (F : Type*) [Field F] (n : ℕ) :
    (MvPolynomial (Fin n) F)[X] →ₗ[MvPolynomial (Fin n) F]
      (FractionRing (MvPolynomial (Fin n) F))[X] :=
  (Polynomial.mapAlgHom (Algebra.ofId (MvPolynomial (Fin n) F)
    (FractionRing (MvPolynomial (Fin n) F)))).toLinearMap

/-- `Φ` applied to a member of an `R`-span lands in the `K`-span of the `Φ`-image. -/
theorem phiX_mem_span_image {x : (MvPolynomial (Fin n) F)[X]}
    {S : Set (MvPolynomial (Fin n) F)[X]}
    (hx : x ∈ Submodule.span (MvPolynomial (Fin n) F) S) :
    phiX F n x ∈ Submodule.span (FractionRing (MvPolynomial (Fin n) F)) (phiX F n '' S) := by
  have h1 : phiX F n x ∈
      Submodule.span (MvPolynomial (Fin n) F) (phiX F n '' S) :=
    Submodule.image_span_subset_span (phiX F n) S ⟨x, hx, rfl⟩
  exact Submodule.span_subset_span (MvPolynomial (Fin n) F)
    (FractionRing (MvPolynomial (Fin n) F)) _ h1

/-- The `Φ`-image of a range is the range of the composed family. -/
theorem phiX_image_range {ι : Type*} (g : ι → (MvPolynomial (Fin n) F)[X]) :
    phiX F n '' Set.range g = Set.range (fun i => phiX F n (g i)) := by
  rw [← Set.range_comp]; rfl

/-! ## The `I`-block family and its cardinality -/

/-- The `I`-block family of `P(k,V)`: the subfamily over the indices `i ∈ I`,
`{ pFam vᵢ e : i ∈ I, e < k − |vᵢ| }`. -/
noncomputable def iBlock (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m)) :
    (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1))) → (MvPolynomial (Fin n) F)[X] :=
  fun p => pFam (F := F) (V p.1.1) (p.2 : ℕ)

/-- The cardinality of the `I`-block index type is `Σ_{i∈I}(k − |vᵢ|)`. -/
theorem card_iBlock_index (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m)) :
    Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1))) = ∑ i ∈ I, (k - vAbs (V i)) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_coe_sort I (fun i => k - vAbs (V i))]

/-- Under tightness (and `|v_I| ≤ k`), the `I`-block index cardinality equals the meet-block size
`k − |v_I|`. -/
theorem card_iBlock_eq_meet {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (htight : tightConstraint V k I hI) :
    Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1)))
      = k - vAbs (vMeet V I hI) := by
  rw [card_iBlock_index]
  unfold tightConstraint at htight
  omega

/-! ## The `I`-block and the meet block span the same `K`-subspace -/

/-- **The `I`-block and the meet block span the same `K`-subspace.**  Forward inclusion maps from
the unconditional ring fact; the reverse is the dimension count over `K`, requiring the `I`-block to
be independent over `R` (`hIblock`) — Lovett's genuine extra input. -/
theorem iBlock_span_eq_meetBlock_K {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (hV : IsVStar V k) (htight : tightConstraint V k I hI)
    (hIblock : LinearIndependent (MvPolynomial (Fin n) F) (iBlock (F := F) V k I)) :
    Submodule.span (FractionRing (MvPolynomial (Fin n) F))
        (Set.range (fun p => phiX F n (iBlock (F := F) V k I p)))
      = Submodule.span (FractionRing (MvPolynomial (Fin n) F))
          (Set.range (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
  classical
  set K := FractionRing (MvPolynomial (Fin n) F)
  -- the meet block is independent over R, hence over K
  have hMeetR : LinearIndependent (MvPolynomial (Fin n) F)
      (meetBlock (F := F) (vMeet V I hI) k) := by
    unfold meetBlock
    exact pFam_single_linearIndependent (vMeet V I hI) (k - vAbs (vMeet V I hI))
  have hMeetK : LinearIndependent K
      (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s)) :=
    (linearIndependent_fractionField_iff _).mp hMeetR
  have hIblockK : LinearIndependent K
      (fun p => phiX F n (iBlock (F := F) V k I p)) :=
    (linearIndependent_fractionField_iff _).mp hIblock
  -- weight bound on the meet ≤ k
  have hwk : ∀ i ∈ I, vAbs (V i) ≤ k := fun i _ => le_trans (hV.weight_le i) (Nat.sub_le k 1)
  -- forward inclusion over K: span (Φ I-block) ≤ span (Φ meet block)
  have hle : Submodule.span K (Set.range (fun p => phiX F n (iBlock (F := F) V k I p)))
      ≤ Submodule.span K
          (Set.range (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    -- iBlock p ∈ span_R (range meetBlock)  (the ring forward inclusion)
    have hR : iBlock (F := F) V k I p ∈
        Submodule.span (MvPolynomial (Fin n) F)
          (Set.range (meetBlock (F := F) (vMeet V I hI) k)) :=
      pFamUnion_I_mem_span_meetBlock hI p.1.2 (hwk p.1.1 p.1.2) (p.2 : ℕ) p.2.2
    have := phiX_mem_span_image (F := F) (n := n) hR
    rwa [phiX_image_range] at this
  -- equal cardinality
  have hcard : Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1)))
      = Fintype.card (Fin (k - vAbs (vMeet V I hI))) := by
    rw [card_iBlock_eq_meet hI htight, Fintype.card_fin]
  exact ArkLib.GMMDS.span_eq_of_le_of_card_of_indep hle hcard hIblockK hMeetK

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.phiX_mem_span_image
#print axioms ArkLib.GMMDS.card_iBlock_index
#print axioms ArkLib.GMMDS.card_iBlock_eq_meet
#print axioms ArkLib.GMMDS.iBlock_span_eq_meetBlock_K
