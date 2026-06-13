/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma25Opening
import ArkLib.Data.CodingTheory.GMMDS.LovettNLtK

/-!
# Lovett's GM-MDS proof: the Lemma 2.5 merge residual, corrected for `n = 0` (#389)

The single remaining open residual of Lovett's Theorem 1.7 is the existence of the Lemma 2.5
witness in a primitive `V*(k)` system.  This file:

1. **Diagnoses a falsity in the current `LovettWitnessExists` residual at `n = 0`** (mirroring the
   earlier `n = k` repair): the empty-vector system `emptyV : Fin 1 → (Fin 0 → ℕ)` is a primitive
   `V*(1)` system, yet `LovettWitness F emptyV 1` is **false** (it demands `1 ≤ 0`).  So
   `LovettWitnessExists` as stated cannot be discharged — `lovettWitnessExists_holds` would be a
   false goal.

2. **Discharges the primitive step at `n = 0` directly** (`lovettHolds_primitive_n0`): a `V*(k)`
   system over `Fin 0` has `m ≤ 1` (Lemma 2.1: any two distinct vectors over the empty coordinate
   set are equal, hence comparable), so `P(k,V)` is the empty family or a single shifted block —
   independent with no witness needed.

3. **Defines the merge residual `LovettMerge`** precisely (the genuine algebraic heart of Lemma
   2.5: in a primitive `V*(k)` system no vector simultaneously has an interior zero and a
   last-coordinate zero), and proves the **corrected** primitive-step reduction
   `LovettPrimitiveStep ⟸ LovettMerge`, routing `n = 0` through (2) and `n ≥ 1` through the
   `witness_or_mergeCandidate` dichotomy + the already-proven `lovettHolds_of_witness`.

The merge-elimination (`LovettMerge`) is thus the entire remaining content of the GM-MDS
conjecture in this development, with the `n = 0` boundary now correctly accounted for.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F]

/-! ## 1. The `n = 0` falsity of the current `LovettWitnessExists` residual -/

/-- The empty-vector system over `Fin 0`: a single vector `Fin 0 → ℕ` (the empty function). -/
def emptyV : Fin 1 → (Fin 0 → ℕ) := fun _ => fun j => j.elim0

theorem emptyV_isVStar : IsVStar emptyV 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; simp [vAbs]
  · intro I hI
    have hIeq : I = {0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      obtain ⟨w, hw⟩ := hI
      exact ⟨by simpa [Fin.fin_one_eq_zero w] using hw, fun x _ => Fin.fin_one_eq_zero x⟩
    subst hIeq
    rw [Finset.sum_singleton]
    have h1 : vAbs (emptyV 0) = 0 := by simp [vAbs]
    have hmeet : vAbs (vMeet emptyV {0} (Finset.singleton_nonempty 0)) = 0 := by simp [vAbs, vMeet]
    rw [h1, hmeet]
  · intro i j; exact j.elim0

theorem emptyV_primitive : ∀ j : Fin 0, ∃ i, emptyV i j = 0 := fun j => j.elim0

/-- **The `n = 0` counterexample to the literal `LovettWitness`.**  Even though `emptyV` is a
primitive `V*(1)` system, the witness `LovettWitness F emptyV 1` is false: it demands the
existence of `hn : 1 ≤ 0`.  Hence `LovettWitnessExists` (which would supply such a witness) is
**not** provable as stated — the `n = 0` boundary must be handled separately. -/
theorem not_lovettWitness_emptyV : ¬ LovettWitness F emptyV 1 := by
  rintro ⟨hn, _, _⟩
  exact absurd hn (by norm_num)

/-! ## 2. The primitive step at `n = 0`, discharged directly -/

/-- A `V*(k)` system over `Fin 0` (with `1 ≤ k`) has at most one vector: over the empty coordinate
set every vector is the empty function, so any two are equal — hence comparable, which Lemma 2.1
(`not_le_of_isVStar`) forbids for *distinct* indices. -/
theorem m_le_one_of_n_zero {m : ℕ} {V : Fin m → (Fin 0 → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) : m ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  -- m ≥ 2: pick the two distinct indices 0 and 1
  have h0 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h; simpa using congrArg (Fin.val) h
  exact not_le_of_isVStar hk hV h0 (fun l => l.elim0)

/-- **The primitive step at `n = 0`.**  A primitive `V*(k)` system over `Fin 0` is independent:
`m ≤ 1`, so `P(k,V)` is either empty (`m = 0`) or one shifted monomial block (`m = 1`), both
linearly independent — no Lemma 2.5 witness is needed (and none exists). -/
theorem lovettHolds_primitive_n0 {m : ℕ} {V : Fin m → (Fin 0 → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) : LovettHolds F V k := by
  classical
  unfold LovettHolds
  rcases Nat.lt_or_ge m 1 with hm0 | hm1
  · -- m = 0: empty family
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm0
    haveI : IsEmpty (Σ i : Fin 0, Fin (k - vAbs (V i))) := by
      constructor; rintro ⟨i, _⟩; exact i.elim0
    exact linearIndependent_empty_type
  · -- m = 1: single block, reindex Σ to Fin and use the base case
    have hm1' : m = 1 := le_antisymm (m_le_one_of_n_zero hk hV) hm1
    subst hm1'
    -- `Σ i : Fin 1, Fin (k - |Vᵢ|) ≃ Fin (k - |V 0|)` via the unique index `0`.
    let e : (Σ i : Fin 1, Fin (k - vAbs (V i))) ≃ Fin (k - vAbs (V 0)) :=
      { toFun := fun p => Fin.fin_one_eq_zero p.1 ▸ p.2
        invFun := fun x => ⟨0, x⟩
        left_inv := by
          rintro ⟨i, x⟩
          obtain rfl : i = 0 := Fin.fin_one_eq_zero i
          rfl
        right_inv := fun x => rfl }
    have hbase : LinearIndependent (MvPolynomial (Fin 0) F)
        (fun x : Fin (k - vAbs (V 0)) => pFam (F := F) (V 0) (x : ℕ)) :=
      pFam_single_linearIndependent (V 0) (k - vAbs (V 0))
    have hcomp : (fun x : Fin (k - vAbs (V 0)) => pFam (F := F) (V 0) (x : ℕ)) ∘ e
        = pFamUnion (F := F) V k := by
      funext p
      obtain ⟨i, x⟩ := p
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    rw [← hcomp]
    exact hbase.comp e e.injective

/-! ## 3. The merge residual `LovettMerge` and the corrected primitive-step reduction -/

/-- **The merge residual** (the genuine algebraic heart of Lovett Lemma 2.5).  In a *primitive*
`V*(k)` system over `Fin n` with `1 ≤ n`, given the full minimal-counterexample induction
hypotheses, NO vector simultaneously carries an interior zero (`j* < n−1`) and a last-coordinate
zero.

`witness_or_mergeCandidate` shows the only obstruction to the Lemma 2.5 witness is exactly such a
"merge candidate"; ruling it out is Lovett's substitution-divisibility argument (kernel in
`LovettSubstitutionDvd`: `a_last ↦ a_{j*}` collapses to dimension `n−1`, a minimal common-factor
-free dependence then forces `(a_{j*} − a_last)` to divide every coefficient, contradiction). -/
def LovettMerge (F : Type*) [Field F] : Prop :=
  ∀ {n m : ℕ} (hn : 1 ≤ n) (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    (∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k') →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) →
    ¬ (∃ (i : Fin m) (j : Fin n), (j : ℕ) < n - 1 ∧ V i j = 0 ∧ V i (lastCoord n hn) = 0)

/-- **The Lemma 2.5 witness exists for `n ≥ 1`, modulo the merge residual.**  When `1 ≤ n`, the
`witness_or_mergeCandidate` dichotomy + `LovettMerge` (which kills the merge alternative) yields
the structured witness `vᵢ₀ = (1,…,1,0)`. -/
theorem lovettWitness_of_merge (hmrg : LovettMerge F) {n m : ℕ} (hn : 1 ≤ n)
    (V : Fin m → (Fin n → ℕ)) (k : ℕ) (hk : 1 ≤ k) (hV : IsVStar V k)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0)
    (IHn : ∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k')
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) :
    LovettWitness F V k := by
  rcases witness_or_mergeCandidate hn hV hprim with hwit | hmerge
  · obtain ⟨i₀, hone⟩ := hwit
    exact ⟨hn, i₀, hone⟩
  · exact absurd hmerge (hmrg hn V k hk hV hprim IHn IHd)

/-- **The primitive step holds, modulo only the merge residual `LovettMerge`.**  This is the
corrected reduction (handling `n = 0` directly), so it is *not* subject to the `n = 0` falsity of
the literal `LovettWitnessExists`.  Discharging `LovettMerge` (Lovett's substitution argument)
closes Theorem 1.7 and the prize route R3. -/
theorem lovettPrimitiveStep_of_merge (hmrg : LovettMerge F) : LovettPrimitiveStep F := by
  intro n m V k hk hV hprim IHn IHd
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; exact lovettHolds_primitive_n0 hk hV
  · exact lovettHolds_of_witness hk hV
      (lovettWitness_of_merge hmrg hnpos V k hk hV hprim IHn IHd) IHd

/-- **Theorem 1.7 (and `LovettPrimitiveCase`, full GM-MDS), modulo the merge residual.** -/
theorem lovettThm17_of_merge (hmrg : LovettMerge F) {n : ℕ} : LovettThm17 F n :=
  lovettThm17_of_primitiveStep (lovettPrimitiveStep_of_merge hmrg)

theorem lovettPrimitiveCase_of_merge (hmrg : LovettMerge F) {n : ℕ} : LovettPrimitiveCase F n :=
  lovettPrimitiveCase_of_primitiveStep (lovettPrimitiveStep_of_merge hmrg)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.emptyV_isVStar
#print axioms ArkLib.GMMDS.not_lovettWitness_emptyV
#print axioms ArkLib.GMMDS.lovettHolds_primitive_n0
#print axioms ArkLib.GMMDS.lovettWitness_of_merge
#print axioms ArkLib.GMMDS.lovettPrimitiveStep_of_merge
#print axioms ArkLib.GMMDS.lovettThm17_of_merge
#print axioms ArkLib.GMMDS.lovettPrimitiveCase_of_merge
