/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import Mathlib.FieldTheory.Finiteness

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemma 2.17 [GG25] is **proven** (with a statement repair: the
paper-faithful rate over the block alphabet `F^s` is `k/(s·n)`, see the docstring);
Theorem 2.18 [GK16] remains an external admit.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`.
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25] (**proven**, statement
  repaired): a nontrivial τ-subspace-design code of rate `ρ = k/(s·n)` has
  `min_{r∈[s]} τ(r) ≥ ρ - 1/n`, via the 1-dimensional-span instantiation + the Singleton
  bound over the block alphabet.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16] (external admit):
  folded RS codes are τ-subspace-design for explicit τ. NOTE: its τ formula inherits the
  same `s`-factor rate convention as the pre-repair L2.17 and should be re-checked against
  ABF26/GK16 before any proof attempt (tracked in the L2.17 repair docstring).

## Deferred

- Univariate multiplicity codes `UM[F, L, k, s]` are referenced in T2.18 but require a
  separate `D_ux` (derivative-of-x) operation; tracked under ABF26-D2.19 / DA.7.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.5 Definition 2.16, Lemma 2.17, Theorem 2.18.
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal

/-- **ABF26 Definition 2.16 [GX13].** A code `C : F^k → (F^s)^n` (here represented as a
subspace of `(ι → Fin s → F)` over `F`) is **τ-subspace-design** if for every `r ∈ ℕ`
and every F-linear subspace `A` of `C` with `dim A ≤ r`,

  `(Σ_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`

where `A_i := { a ∈ A : a_i = 0^s }` is the subspace of `A` whose codewords vanish at
position `i`. Here `A_i` is realised as `A ⊓ ker(eval_i)`, the intersection of `A`
with the kernel of the linear map evaluating the `i`-th coordinate. -/
def IsSubspaceDesign {ι : Type} [Fintype ι]
    {F : Type} [Field F] (s : ℕ) (τ : ℕ → ℝ)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ r : ℕ, ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    Module.finrank F A ≤ r →
    (∑ i : ι,
        (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) /
        Fintype.card ι ≤
      Module.finrank F A * τ r

/-- **Bridge: kernel of the `i`-th projection equals the comprehension `{a | a i = 0}`.**

The subspace `A_i := {a ∈ A : a_i = 0^s}` from the paper's `IsSubspaceDesign` definition
is `A ⊓ ker(LinearMap.proj i)`. This lemma confirms the underlying set: a word
`a : ι → Fin s → F` lies in `ker(proj i)` iff `a i = 0`. Combined with `Submodule.inf_*`
this lets downstream proofs rewrite freely between the technical `ker(proj i)` form (used
in the `IsSubspaceDesign` definition for type-class reasons) and the paper's
comprehension form. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`. -/
private lemma span_inf_ker_proj_of_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ} {a : ι → Fin s → F} {i : ι} (hai : a i = 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) =
      Submodule.span F {a} :=
  inf_eq_left.mpr <| Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    simp [LinearMap.mem_ker, LinearMap.proj_apply, hai]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`. -/
private lemma span_inf_ker_proj_of_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ} {a : ι → Fin s → F} {i : ι} (hai : a i ≠ 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx_span, hx_ker⟩ := Submodule.mem_inf.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx_span
  have h0 : c • a i = 0 := by
    simpa [LinearMap.mem_ker, LinearMap.proj_apply] using hx_ker
  rcases smul_eq_zero.mp h0 with hc | h
  · simp [hc]
  · exact absurd h hai

/-- **ABF26 Lemma 2.17 [GG25]** (statement repaired — see below). For any *nontrivial*
τ-subspace-design code `C : F^k → (F^s)^n` of rate `ρ := k/(s·n)`, the profile `τ` is
lower-bounded by `ρ - 1/n` over the paper's range `r ∈ [s] = {1, …, s}`:

  `min_{r ∈ [s]} τ(r) ≥ ρ - 1/n` .

**Statement repair (2026-06-04).** The previous (admitted) form used `ρ := k/n`.
ABF26 Definition 2.5 fixes the rate of a code over alphabet `Σ` as `log_|Σ| |C| / n`;
for an F-additive code over `Σ = F^s` with `|C| = |F|^k` this is `k/(s·n)`, not `k/n`.
The `k/n` form is **false for `s ≥ 2`**: the full code `C = (F^s)^n` is
`(1 - 1/n)`-subspace-design — for any `A ≤ C`,
`Σ_i dim A_i = n·dim A - Σ_i rank(eval_i) ≤ (n-1)·dim A` because
`⋂_i ker(eval_i) = ⊥` forces `Σ_i rank(eval_i) ≥ dim A` — yet the `k/n` form would
demand `τ(r) ≥ s - 1/n > 1 - 1/n`. At the corrected rate the full code is instead the
tightness witness: `k/(s·n) - 1/n = 1 - 1/n`.

**Nontriviality `C ≠ ⊥`** is paper-implicit (a code is a map `F^k → (F^s)^n` with
`k ≥ 1`): for `C = ⊥` the design property constrains nothing (the only subspace is
`A = ⊥`, giving `0 ≤ 0`), while the conclusion would still assert `τ(r) ≥ -1/n`,
which fails for e.g. `τ ≡ -1`.

The quantifier is restricted to `r ∈ Finset.Icc 1 s` to match the paper's `[s]`
notation: outside this range the `IsSubspaceDesign` predicate places no
constraint on `τ`, so the bound is vacuous for `r = 0` (where `A ≤ C` with
`finrank A ≤ 0` forces `A = ⊥`, making the design inequality `0 ≤ 0 · τ(0)`
trivially satisfied by any `τ(0)` including ones violating the lower bound).

**Proof sketch.** Take a minimum-weight nonzero codeword `a` (the minimum distance
`d` of `C` is achieved by a pair `u ≠ v`; set `a := u - v`). Instantiate the design
property at the 1-dimensional `A := span{a}` (`dim A = 1 ≤ r`): then `A_i = A` iff
`a i = 0` and `A_i = ⊥` otherwise, so `Σ_i dim A_i = n - wt(a) = n - d`, giving
`τ(r) ≥ (n-d)/n`. The Singleton bound over the block alphabet `F^s`
(`q^k ≤ (q^s)^{n-d+1}`) gives `k ≤ s·(n-d+1)`, hence `(n-d)/n ≥ k/(s·n) - 1/n`. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (h_nontriv : C ≠ ⊥) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / ((s : ℝ) * Fintype.card ι) -
        1 / Fintype.card ι := by
  intro r hr
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  -- ① A nonzero codeword exists, so the minimum distance is achieved by some pair.
  obtain ⟨a₀, ha₀C, ha₀ne⟩ := (Submodule.ne_bot_iff C).mp h_nontriv
  have hSne : {d | ∃ u ∈ (C : Set (ι → Fin s → F)), ∃ v ∈ (C : Set (ι → Fin s → F)),
      u ≠ v ∧ hammingDist u v = d}.Nonempty :=
    ⟨hammingDist a₀ 0, a₀, ha₀C, 0, C.zero_mem, ha₀ne, rfl⟩
  have hd_mem : Code.minDist (C : Set (ι → Fin s → F)) ∈
      {d | ∃ u ∈ (C : Set (ι → Fin s → F)), ∃ v ∈ (C : Set (ι → Fin s → F)),
        u ≠ v ∧ hammingDist u v = d} := by
    rw [Code.minDist]
    exact Nat.sInf_mem hSne
  obtain ⟨u, huC, v, hvC, huv_ne, huv_d⟩ := hd_mem
  -- The minimum-weight nonzero codeword `a := u - v`.
  have haC : u - v ∈ C := C.sub_mem huC hvC
  have ha_ne : u - v ≠ 0 := sub_ne_zero.mpr huv_ne
  have ha_norm : hammingNorm (u - v) = Code.minDist (C : Set (ι → Fin s → F)) := by
    rw [← neg_add_eq_sub, ← hammingDist_eq_hammingNorm, hammingDist_comm]
    exact huv_d
  have hd_pos : 1 ≤ Code.minDist (C : Set (ι → Fin s → F)) :=
    Nat.one_le_iff_ne_zero.mpr fun h0 =>
      huv_ne (hammingDist_eq_zero.mp (huv_d.trans h0))
  have hd_le_n : Code.minDist (C : Set (ι → Fin s → F)) ≤ Fintype.card ι := by
    rw [← huv_d]
    exact hammingDist_le_card_fintype
  -- ② Instantiate the design property at the 1-dimensional `A := span{a}`.
  have hA_le : Submodule.span F {u - v} ≤ C :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr haC)
  have hA_rank : Module.finrank F (Submodule.span F {u - v}) = 1 :=
    finrank_span_singleton ha_ne
  have hdesign := h r (Submodule.span F {u - v}) hA_le (by rw [hA_rank]; exact hr1)
  rw [hA_rank] at hdesign
  -- ③ Per-coordinate ranks: `dim A_i = 1` iff the block `(u-v) i` vanishes.
  have hterm : ∀ i : ι,
      (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ) =
        if (u - v) i = 0 then 1 else 0 := by
    intro i
    by_cases hai : (u - v) i = 0
    · rw [span_inf_ker_proj_of_eq_zero hai, hA_rank, if_pos hai]
      norm_num
    · rw [span_inf_ker_proj_of_ne_zero hai, if_neg hai]
      simp
  -- ④ The design sum is the number of vanishing blocks, `n - d`.
  have hsum : (∑ i : ι,
      (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ)) =
      (Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Finset.sum_boole]
    have hsplit : ({i | (u - v) i = 0} : Finset ι).card +
        ({i | (u - v) i ≠ 0} : Finset ι).card = Fintype.card ι := by
      simpa using Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun i : ι => (u - v) i = 0)
    have hnorm_card : ({i | (u - v) i ≠ 0} : Finset ι).card =
        Code.minDist (C : Set (ι → Fin s → F)) := by
      rw [← ha_norm]; rfl
    have hzero_card : ({i | (u - v) i = 0} : Finset ι).card =
        Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) := by omega
    rw [hzero_card]
    push_cast [Nat.cast_sub hd_le_n]
    ring
  have hkey : ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
      (Fintype.card ι : ℝ) ≤ τ r := by
    calc ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
        (Fintype.card ι : ℝ)
        = (∑ i : ι,
            (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
                (LinearMap.ker
                  (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
                Submodule F (ι → Fin s → F))) : ℝ)) / (Fintype.card ι : ℝ) := by
          rw [hsum]
      _ ≤ (1 : ℕ) * τ r := hdesign
      _ = τ r := by norm_num
  -- ⑤ Singleton bound over the block alphabet `F^s`: `k ≤ s·(n - d + 1)`.
  have hsingleton : Module.finrank F C ≤
      s * (Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
    haveI : Fintype ↥(C : Set (ι → Fin s → F)) := Fintype.ofFinite _
    have hsb := singleton_bound (C : Set (ι → Fin s → F))
    rw [Subsingleton.elim (Fintype.ofFinite ↥(C : Set (ι → Fin s → F)))
      ‹Fintype ↥(C : Set (ι → Fin s → F))›,
      Subsingleton.elim (Fintype.ofFinite (Fin s → F)) inferInstance] at hsb
    have hcardC : Fintype.card ↥(C : Set (ι → Fin s → F)) =
        Fintype.card F ^ Module.finrank F C := by
      rw [Module.card_eq_pow_finrank (K := F)]
      rfl
    have hcardA : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
      rw [Fintype.card_fun, Fintype.card_fin]
    rw [hcardC, hcardA, Code.dist_eq_minDist] at hsb
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hexp : Fintype.card ι - (Code.minDist (C : Set (ι → Fin s → F)) - 1) =
        Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) + 1 := by omega
    rw [hexp, ← pow_mul] at hsb
    exact (Nat.pow_le_pow_iff_right hq).mp hsb
  -- ⑥ Final arithmetic: `k/(s·n) - 1/n ≤ (n-d)/n ≤ τ r`.
  have hs_pos : (0 : ℝ) < s := by
    have h1s : 1 ≤ s := le_trans hr1 hrs
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1s
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  rw [ge_iff_le]
  have hcast : (Module.finrank F C : ℝ) ≤
      (s : ℝ) * ((Fintype.card ι : ℝ) -
        Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
    calc (Module.finrank F C : ℝ)
        ≤ ((s * (Fintype.card ι -
            Code.minDist (C : Set (ι → Fin s → F)) + 1) : ℕ) : ℝ) := by
          exact_mod_cast hsingleton
      _ = (s : ℝ) * ((Fintype.card ι : ℝ) -
            Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
          push_cast [Nat.cast_sub hd_le_n]
          ring
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_posR
  calc (Module.finrank F C : ℝ) / ((s : ℝ) * Fintype.card ι) - 1 / Fintype.card ι
      ≤ ((s : ℝ) * ((Fintype.card ι : ℝ) -
          Code.minDist (C : Set (ι → Fin s → F)) + 1)) /
          ((s : ℝ) * Fintype.card ι) - 1 / Fintype.card ι := by
        gcongr
    _ = ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
          (Fintype.card ι : ℝ) := by
        field_simp
        ring
    _ ≤ τ r := hkey

/-- **ABF26 Theorem 2.18 [GK16].** Both folded Reed-Solomon codes and univariate
multiplicity codes are τ-subspace-design for an explicit τ:

  `τ(r) := s · ρ / (s - r + 1)` for `r ∈ [s] = {1, …, s}`, and `τ(r) := 1` otherwise.

Note: `[s]` in the paper denotes `{1, …, s}` (one-based), which we encode in Lean as
`Finset.Icc 1 s`. With this convention `τ(1) = ρ` and `τ(s) = s · ρ`, matching the paper's
boundary values.

The FRS case requires `(L, s)`-admissibility of `ω`; the multiplicity case requires
`|F| > n` and `char(F) > ρ·s·n > s`. We state only the FRS half here; the multiplicity
half is gated on `D2.19 / DA.7` (univariate-multiplicity definition), which is tracked
separately. Admitted as an external result. -/
theorem frs_is_subspaceDesign_gk16
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (_hL_dom : ∀ i : ι, domain i ∈ L)
    (_hω : ReedSolomon.Folded.Admissible L s ω) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  sorry -- ABF26-T2.18 (FRS half); external admit [GK16].

end CodingTheory
