/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing
import ArkLib.Data.CodingTheory.ProximityGap.StepanovHasseInterface

/-!
# Issue #232/#389 — the Stepanov–Weil engine for the obstruction-form auxiliary.

This file welds the two halves of Stepanov's method, now that **both** are unconditional:

* the **non-vanishing** (`StepanovNonVanishing.obstruction_forces_trivial`): a nonzero
  obstruction-form auxiliary `R = subq A₀ + g^((q−1)/2)·subq A₁` stays nonzero (no genus
  hypothesis — the squarefree / integrally-closed argument);
* the **counting** (`StepanovHasseInterface.stepanov_card_mul_lt_of_hasse`): a nonzero `R` of
  degree `< D` vanishing to Hasse-order `M` at every point of `V` forces `|V|·M < D`.

The weld `weil_form_card_lt` is the Stepanov point-count for the Weil-relevant auxiliary form
**with the non-vanishing discharged for free**: a concrete application now only has to (i) build
the auxiliary `(A₀, A₁)` by a dimension count (so that it is not identically zero and its combined
square-blocks fit base-`q`), (ii) check it vanishes to Hasse-order `M` at `V`, and (iii) bound its
degree by `D`; the bound `|V|·M < D` is then automatic. The remaining mathematical content of the
full Weil bound — the explicit auxiliary construction with the `√q`-strength degree accounting — is
the only piece left, and it is elementary linear algebra plus degree bookkeeping, not a
Mathlib-lacking obstruction.

## Honest scope
Even the full Weil bound recovers only the **Johnson** radius `√ρ`, never the past-Johnson `δ*`
prize (`CensusDomination`, the sub-Johnson supply wall, stays the open core of #389). This file is
infrastructure: it carries no `√q`-strength claim by itself.

All results `sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Polynomial
open ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.StepanovHasseInterface

namespace ArkLib.ProximityGap.StepanovWeilEngine

variable {F : Type*} [Field F] [Fintype F]

/-- **The Stepanov–Weil engine (non-vanishing discharged).** For `g` squarefree of positive degree
over a finite field with `q = |F|` odd: any obstruction-form auxiliary
`R = subq A₀ + g^((q−1)/2)·subq A₁` that is

* not trivially zero (`A₀, A₁` not both zero),
* has combined square-blocks `C g·A₀² − ĝ·A₁²` of `X`-degree `< q` (so base-`q` faithfulness
  applies — this is the genuine `deg_X A_i < q/2 − deg g` regime),
* has `natDegree < D`, and
* vanishes to Hasse-order `M` at every point of `V`,

forces `|V|·M < D`. The non-vanishing `R ≠ 0` is supplied for free by `obstruction_forces_trivial`;
no genus / Hasse–Weil hypothesis is needed. -/
theorem weil_form_card_lt
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    (A0 A1 : Polynomial (Polynomial F))
    (hA : ¬ (A0 = 0 ∧ A1 = 0))
    (hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < Fintype.card F)
    (V : Finset F) {M D : ℕ}
    (hdegR : (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1).natDegree < D)
    (hvan : ∀ a ∈ V, ∀ k < M, (hasseDeriv k (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1)).eval a = 0) :
    V.card * M < D := by
  set R := subq (Fintype.card F) A0
    + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1 with hRdef
  have hR : R ≠ 0 := by
    intro h
    exact hA (obstruction_forces_trivial g hg hdeg hq_odd A0 A1 hblk h)
  exact stepanov_card_mul_lt_of_hasse V ⟨R, hR, hdegR, hvan⟩

/-- Divided form: with `0 < M`, `|V| ≤ (D − 1) / M`. -/
theorem weil_form_card_le
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    (A0 A1 : Polynomial (Polynomial F))
    (hA : ¬ (A0 = 0 ∧ A1 = 0))
    (hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < Fintype.card F)
    (V : Finset F) {M D : ℕ}
    (hMpos : 0 < M)
    (hdegR : (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1).natDegree < D)
    (hvan : ∀ a ∈ V, ∀ k < M, (hasseDeriv k (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1)).eval a = 0) :
    V.card ≤ (D - 1) / M := by
  have h := weil_form_card_lt g hg hdeg hq_odd A0 A1 hA hblk V hdegR hvan
  rw [Nat.le_div_iff_mul_le hMpos]
  omega

/-- **Degree bound for the Weil-form auxiliary.** With `X`-blocks of `A₀, A₁` of degree `< q`,
`deg R ≤ max(q·deg_Y A₀ + (q−1),  ((q−1)/2)·deg g + q·deg_Y A₁ + (q−1))`. This is the `D` that the
counting half consumes; choosing `deg_Y Aᵢ` and the block bound to balance against the dimension
count is the (elementary) `√q` optimization that completes the full Weil bound. -/
theorem natDegree_weil_form_le
    (g : F[X]) (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree < Fintype.card F)
    (h1 : ∀ j, (A1.coeff j).natDegree < Fintype.card F) :
    (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1).natDegree
      ≤ max (Fintype.card F * A0.natDegree + (Fintype.card F - 1))
          (((Fintype.card F - 1) / 2) * g.natDegree
            + (Fintype.card F * A1.natDegree + (Fintype.card F - 1))) := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le_max ?_ ?_)
  · exact natDegree_subq_le _ A0 h0
  · refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_pow]
    exact Nat.add_le_add_left (natDegree_subq_le _ A1 h1) _

/-! ## The two-component dimension-count construction of the obstruction-form auxiliary.

`exists_stepanov_auxiliary_pair`: a nonzero pair `(A₀, A₁)` with `X`-blocks of degree `≤ A` and
`Y`-degree `< ℓ`, whose Weil-form auxiliary `R = subq A₀ + g^((q−1)/2)·subq A₁` vanishes to
Hasse-order `M` at every point of `V`, exists as soon as the dimension `2·ℓ·(A+1)` exceeds the
number of conditions `|V|·M`. Pure rank-nullity (`ker_ne_bot_of_finrank_lt`) on the linear map
`(b₀, b₁) ↦ (a, k) ↦ E^k(R)(a)`. Non-triviality of `(A₀, A₁)` comes from injectivity of the
block-to-polynomial map, NOT from the (separately proven) non-vanishing of `R`. -/
section Construction

/-- `subq` as an `F`-linear map (it is the `F[X]`-algebra map `aeval (X^q)`). -/
noncomputable def subqLin (q : ℕ) : Polynomial (Polynomial F) →ₗ[F] Polynomial F :=
  (Polynomial.aeval (X ^ q : Polynomial F)).toLinearMap.restrictScalars F

theorem subqLin_eq (q : ℕ) (A : Polynomial (Polynomial F)) : subqLin q A = subq q A := by
  simp only [subqLin, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply,
    Polynomial.aeval_def]
  rfl

/-- The block-data `→ F[X][Y]` map: `b ↦ ∑_{j<ℓ} (b j)·Y^j` (each block `b j ∈ F[X]_{<A+1}`). -/
noncomputable def blockPoly (ℓ A : ℕ) :
    (Fin ℓ → Polynomial.degreeLT F (A + 1)) →ₗ[F] Polynomial (Polynomial F) :=
  ∑ j : Fin ℓ, ((Polynomial.monomial (j : ℕ)).restrictScalars F).comp
    (((Polynomial.degreeLT F (A + 1)).subtype).comp (LinearMap.proj j))

theorem blockPoly_apply (ℓ A : ℕ) (b : Fin ℓ → Polynomial.degreeLT F (A + 1)) :
    blockPoly ℓ A b = ∑ j : Fin ℓ, Polynomial.monomial (j : ℕ) (b j : Polynomial F) := by
  rw [blockPoly, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [LinearMap.comp_apply])

theorem blockPoly_coeff (ℓ A : ℕ) (b : Fin ℓ → Polynomial.degreeLT F (A + 1)) (i : Fin ℓ) :
    (blockPoly ℓ A b).coeff (i : ℕ) = (b i : Polynomial F) := by
  rw [blockPoly_apply, finset_sum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro j _ hj; rw [Polynomial.coeff_monomial, if_neg (fun h => hj (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem blockPoly_inj (ℓ A : ℕ) : Function.Injective (blockPoly (F := F) ℓ A) := by
  intro b b' hbb; funext i; rw [Subtype.ext_iff]
  rw [← blockPoly_coeff ℓ A b i, ← blockPoly_coeff ℓ A b' i, hbb]

theorem blockPoly_coeff_natDegree_le (ℓ A : ℕ) (b : Fin ℓ → Polynomial.degreeLT F (A + 1)) (i : ℕ) :
    ((blockPoly ℓ A b).coeff i).natDegree ≤ A := by
  by_cases hi : i < ℓ
  · rw [show i = ((⟨i, hi⟩ : Fin ℓ) : ℕ) from rfl, blockPoly_coeff]
    have hb := (b ⟨i, hi⟩).2
    rw [Polynomial.mem_degreeLT] at hb
    by_cases hz : (b ⟨i, hi⟩ : Polynomial F) = 0
    · rw [hz]; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hb; omega
  · rw [blockPoly_apply, finset_sum_coeff, Finset.sum_eq_zero]
    · simp
    · intro j _; rw [Polynomial.coeff_monomial, if_neg (by intro h; omega)]

/-- Per-component Weil-form builder `b ↦ subq (blockPoly b)`. -/
noncomputable def Pbuild (q ℓ A : ℕ) : (Fin ℓ → Polynomial.degreeLT F (A + 1)) →ₗ[F] Polynomial F :=
  (subqLin q).comp (blockPoly ℓ A)

/-- The full Weil-form builder over the pair domain. -/
noncomputable def toR (g : Polynomial F) (q ℓ A : ℕ) :
    ((Fin ℓ → Polynomial.degreeLT F (A + 1)) × (Fin ℓ → Polynomial.degreeLT F (A + 1)))
      →ₗ[F] Polynomial F :=
  (Pbuild q ℓ A).comp (LinearMap.fst F _ _)
    + ((LinearMap.mulLeft F (g ^ ((q - 1) / 2))).comp (Pbuild q ℓ A)).comp (LinearMap.snd F _ _)

theorem toR_apply (g : Polynomial F) (q ℓ A : ℕ)
    (bb : (Fin ℓ → Polynomial.degreeLT F (A + 1)) × (Fin ℓ → Polynomial.degreeLT F (A + 1))) :
    toR g q ℓ A bb
      = subq q (blockPoly ℓ A bb.1) + (g ^ ((q - 1) / 2)) * subq q (blockPoly ℓ A bb.2) := by
  simp only [toR, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.mulLeft_apply, Pbuild, subqLin_eq]

/-- The jet-evaluation map `Ψ ↦ (a, k) ↦ E^k(Ψ)(a)`. -/
noncomputable def jetEvalAt (V : Finset F) (M : ℕ) : Polynomial F →ₗ[F] (↥V × Fin M → F) :=
  LinearMap.pi (fun p => (Polynomial.leval (p.1 : F)).comp (hasseDeriv (p.2 : ℕ)))

theorem jetEvalAt_apply (V : Finset F) (M : ℕ) (Ψ : Polynomial F) (p : ↥V × Fin M) :
    jetEvalAt V M Ψ p = (hasseDeriv (p.2 : ℕ) Ψ).eval (p.1 : F) := rfl

theorem finrank_construction_domain (ℓ A : ℕ) :
    Module.finrank F
        ((Fin ℓ → Polynomial.degreeLT F (A + 1)) × (Fin ℓ → Polynomial.degreeLT F (A + 1)))
      = 2 * (ℓ * (A + 1)) := by
  rw [Module.finrank_prod]
  simp only [Module.finrank_pi_fintype,
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (A + 1)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem finrank_construction_codomain (V : Finset F) (M : ℕ) :
    Module.finrank F (↥V × Fin M → F) = V.card * M := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]

/-- **The two-component Stepanov auxiliary, constructed by dimension count.** Whenever
`|V|·M < 2·ℓ·(A+1)`, there is a nonzero pair `(A₀, A₁)` (Y-degree `< ℓ`, `X`-blocks of degree `≤ A`)
whose Weil-form auxiliary vanishes to Hasse-order `M` at every point of `V`. Pure rank-nullity. -/
theorem exists_stepanov_auxiliary_pair (g : Polynomial F) (q ℓ A : ℕ) (V : Finset F) (M : ℕ)
    (hdim : V.card * M < 2 * (ℓ * (A + 1))) :
    ∃ A0 A1 : Polynomial (Polynomial F),
      ¬ (A0 = 0 ∧ A1 = 0) ∧
      (∀ j, (A0.coeff j).natDegree ≤ A) ∧ (∀ j, (A1.coeff j).natDegree ≤ A) ∧
      (∀ a ∈ V, ∀ k < M,
        (hasseDeriv k (subq q A0 + (g ^ ((q - 1) / 2)) * subq q A1)).eval a = 0) := by
  set Φ := (jetEvalAt V M).comp (toR g q ℓ A) with hΦ
  have hlt : Module.finrank F (↥V × Fin M → F)
      < Module.finrank F
        ((Fin ℓ → Polynomial.degreeLT F (A + 1)) × (Fin ℓ → Polynomial.degreeLT F (A + 1))) := by
    rw [finrank_construction_codomain, finrank_construction_domain]; exact hdim
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨bb, hbbmem, hbbne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨blockPoly ℓ A bb.1, blockPoly ℓ A bb.2, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩
    apply hbbne
    have hb0 : bb.1 = 0 := blockPoly_inj ℓ A (h0.trans (map_zero _).symm)
    have hb1 : bb.2 = 0 := blockPoly_inj ℓ A (h1.trans (map_zero _).symm)
    exact Prod.ext hb0 hb1
  · exact blockPoly_coeff_natDegree_le ℓ A bb.1
  · exact blockPoly_coeff_natDegree_le ℓ A bb.2
  · intro a ha k hk
    have hΦ0 : Φ bb = 0 := by rwa [LinearMap.mem_ker] at hbbmem
    have hcf := congrFun hΦ0 (⟨a, ha⟩, ⟨k, hk⟩)
    rw [hΦ, LinearMap.comp_apply, jetEvalAt_apply, toR_apply] at hcf
    simpa using hcf

end Construction

end ArkLib.ProximityGap.StepanovWeilEngine

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_form_card_lt
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_form_card_le
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.natDegree_weil_form_le
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.exists_stepanov_auxiliary_pair
