/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemmas 2.17 [GG25] and Theorem 2.18 [GK16] are stated as external
admits.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements (external admits)

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`.
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25]: τ-subspace-design
  code of rate `ρ` has `min_r τ(r) ≥ ρ - 1/n`.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16]: folded RS codes
  are τ-subspace-design for explicit τ.

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

/-- **ABF26 Lemma 2.17 [GG25].** For any τ-subspace-design code of rate `ρ`, the
profile `τ` is lower-bounded by `ρ - 1/n` over the paper's range `r ∈ [s] = {1, …, s}`:

  `min_{r ∈ [s]} τ(r) ≥ ρ - 1/n` .

The quantifier is restricted to `r ∈ Finset.Icc 1 s` to match the paper's `[s]`
notation: outside this range the `IsSubspaceDesign` predicate places no
constraint on `τ`, so the bound is vacuous for `r = 0` (where `A ≤ C` with
`finrank A ≤ 0` forces `A = ⊥`, making the design inequality `0 ≤ 0 · τ(0)`
trivially satisfied by any `τ(0)` including ones violating the lower bound).

**STATEMENT DEFECT — wrong `ρ` normalization (found 2026-06-04, counterexample below).**
The rate `ρ` here is written `(finrank F C)/Fintype.card ι = dim_F C / n`. That is
`s` times too large: the paper's rate is the *per-`F^s`-symbol* rate
`ρ = dim_F C / (s · n)` (alphabet `F^s`, block length `n`), so `dim_F C / n = s · ρ`.

*Counterexample to the statement as written.* Take `F = GF(2)`, `s = 2`, `n = 3`,
`C = ⊤` the full space `(F²)³ = F⁶`. The minimal valid design profile is
`τ*(r) = max_{1 ≤ dim A ≤ r} (∑_i dim Aᵢ)/(n · dim A)`; at `r = 1`, `τ*(1)` is maximised
by a weight-1 codeword (nonzero in one of the three blocks), giving
`τ*(1) = (n - 1)/n = 2/3`. The current RHS demands `τ(1) ≥ dim_F C / n − 1/n = 6/3 − 1/3
= 5/3 > 2/3`. So `τ = τ*` witnesses `IsSubspaceDesign` while violating the conclusion at
`r = 1`. With the corrected per-symbol `ρ = dim_F C/(s·n) = 1`, the RHS is `1 − 1/3 = 2/3
= τ*(1)`, consistent. **The fix is to divide by `s · Fintype.card ι` (guard `s ≠ 0`).**

**Exact missing ingredient (citation upgrade), even after the normalization fix.**
The 1-dimensional witness route (`A = span{c}` for a minimum-block-weight `c`) only
yields `τ(r) ≥ 1 − d_min/n`, which via the alphabet-`F^s` Singleton bound
`d_min ≤ n − dim_F C/s + 1` gives `τ(r) ≥ ρ − 1/n` *only* when `dim A` scales with `ρ`,
i.e. it reaches the bound at best as `ρ/s − 1/n` from a single codeword (a factor-`s`
short — sharper than the prior "only `1 − δ_min`" note). The genuine GG25 proof needs
**dimension-averaging over an `r`-dimensional subspace `A ≤ C`**: an existence/averaging
principle over the Grassmannian of `r`-dim subspaces producing an `A` with
`(1/n) ∑_i dim Aᵢ ≥ dim A · (ρ − 1/n)`, together with the GG25 global rank identity
`∑_i rank(proj_i restricted to C) ≤ dim_F C · (1 + (n−1)/n)`-style counting. Neither
the random / generic-subspace expectation machinery nor that rank identity exists
in-tree (mathlib has `Module.finrank` rank-nullity per map, but not the averaged
Grassmannian existence). This is the irreducible paper development.

Admitted as an external result; statement left at the as-published (mis-normalised) form
pending the owner's choice of normalization, with the defect and the fix recorded here. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / Fintype.card ι - 1 / Fintype.card ι := by
  -- ABF26-L2.17; external admit [GG25]. Statement defect (factor-s ρ; counterexample in
  -- docstring) AND a genuine missing development. Three in-tree routes, each blocked:
  --
  -- SKELETON A (1-dim min-weight witness). A := span{c}, c of min block-weight, dimA=1≤r.
  --   Design ineq ⇒ τ(r) ≥ 1 − wt(c)/n = 1 − d_min/n; Singleton (alphabet F^s) ⇒ ≥ ρ/s − 1/n.
  --   BLOCKED: a factor s short of the (corrected) ρ − 1/n; a 1-dim witness cannot scale with ρ.
  --
  -- SKELETON B (r-dim rank-nullity witness). dim(A ⊓ ker_i) ≥ dim A − s (proj_i into F^s);
  --   ∑_i ≥ n(dim A − s) ⇒ τ(r) ≥ 1 − s/dim A. BLOCKED: for r ≤ s, dim A ≤ s ⇒ ≤ 0 (vacuous).
  --
  -- SKELETON C (GG25 dimension-averaging — correct route). Average dim(A_i) over a generic
  --   r-dim A ≤ C to extract A with (1/n)∑_i dim A_i ≥ dim A·(ρ − 1/n); close via design ineq.
  --   BLOCKED: needs Grassmannian averaging/existence + GG25 global rank identity; both ABSENT.
  --
  -- The conclusion is additionally false at small r under the current ρ normalization (see
  -- the counterexample). Tagged sorry / external admit; normalization left for owner.
  sorry

/-- **ABF26 Theorem 2.18 [GK16].** Both folded Reed-Solomon codes and univariate
multiplicity codes are τ-subspace-design for an explicit τ:

  `τ(r) := s · ρ / (s - r + 1)` for `r ∈ [s] = {1, …, s}`, and `τ(r) := 1` otherwise.

Note: `[s]` in the paper denotes `{1, …, s}` (one-based), which we encode in Lean as
`Finset.Icc 1 s`. With this convention `τ(1) = ρ` and `τ(s) = s · ρ`, matching the paper's
boundary values.

The FRS case requires `(L, s)`-admissibility of `ω`; the multiplicity case requires
`|F| > n` and `char(F) > ρ·s·n > s`. We state only the FRS half here; the multiplicity
half is gated on `D2.19 / DA.7` (univariate-multiplicity definition), which is tracked
separately. Admitted as an external result.

**Normalization note (consistent with the L2.17 defect above).** This `τ` uses
`s · k / n` (with `dim_F (frsCode) = k`, so `k/n = dim_F C / n = s · ρ_persymbol`), giving
`τ(1) = k/n = ρ_intree` and `τ(s) = s·k/n`. It is therefore internally consistent with
`subspaceDesign_tau_lower`'s *current* `ρ = dim_F C / n` convention (so the lower bound
`τ(1) ≥ ρ_intree − 1/n` would read `k/n ≥ k/n − 1/n`, true). If L2.17's `ρ` is fixed to
the paper's per-symbol `dim_F C/(s·n)`, this `τ` must be rescaled by `1/s` in lockstep
(`τ(r) := k/(n·(s−r+1))`). The two statements share one normalization decision.

**Exact missing ingredients (citation upgrade).** Proving `IsSubspaceDesign` for `frsCode`
requires, for every `A ≤ frsCode domain k s ω` with `dim_F A ≤ r`, the GK16 bound
`∑_i dim_F(A ⊓ ker proj_i) ≤ dim_F A · n · τ(r)`. The GK16 argument is:
(1) lift `A` to a space of `degreeLT F k` polynomials via `frsEvalOnPoints` (the in-tree
    `mem_frsCode_iff` / `dim_frsCode` give the lift and `dim A = #polys`);
(2) a codeword vanishes at coordinate `i` iff its polynomial `p` satisfies
    `p(ω^j · domain i) = 0` for all `j < s`, i.e. `∏_{j<s}(X − ω^j·domain i) ∣ p`;
(3) the *Wronskian / folded-Vandermonde non-degeneracy* under `Admissible ω`: at most
    `s − r + 1` of the `n` folded blocks can simultaneously annihilate an `r`-dim space of
    degree-`<k` polynomials (this is the GK16 linear-algebra core, a rank bound on the
    block-Vandermonde matrices). Step (3) — the folded-Vandermonde rank bound — is the
    irreducible external: ArkLib has the FRS evaluation map and `degreeLT` dimension, but
    **not** the multi-point/Wronskian Vandermonde rank lemma over folded orbits. That lemma
    (≈ several hundred lines: Vandermonde minors, derivative/Wronskian non-vanishing under
    `Admissible`) is the entire content of T2.18 and is not reducible to in-tree lemmas.
    Statement-level: T2.18 is a self-contained GK16 development, not a corollary of any
    present result. Tagged sorry / external admit. -/
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
  -- ABF26-T2.18 (FRS half); external admit [GK16]. Standalone GK16 development; the
  -- irreducible ingredient is the folded-Vandermonde / Wronskian rank bound under
  -- `Admissible ω` (≤ s−r+1 blocks annihilate an r-dim degree-<k space). See docstring.
  sorry

end CodingTheory
