/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SoundnessConverse
import ArkLib.Data.Probability.Instances
import Mathlib.Algebra.Polynomial.Roots

/-!
# LogUp Protocol 2 — the *corrected* outer-phase soundness (issue #13)

`Logup.OuterSoundnessResidual` (`Security/SubPhaseSplit.lean`) is **degenerate**. Its intermediate
language is `midLanguage`, which after the outer phase always *contains* the (verifier-honest)
after-outer statement: with the honest helper/multiplicity oracles the sumcheck claim is the grand
sum, which the algebra makes a tautology, so demanding `Pr[outer accepts ↦ midLanguage] ≤ ε` for a
genuinely *bad* input is false — the outer phase always "lands" in `midLanguage`. The genuine
soundness obstruction is not the *outer phase landing in a language*, it is the **algebraic check
polynomial vanishing at the random challenge**.

This file states and *proves* the corrected, non-degenerate outer soundness statement:

> for a **bad** lookup input (`∉ inputRelation`), the cleared grand-sum check polynomial
> `grandSumCheckPoly oStmt` is *nonzero* (`grandSumCheckPoly_ne_zero_of_bad_lookup`), so a uniformly
> sampled outer challenge `x` makes the check **appear to pass** — i.e. lands the after-outer
> statement in the genuine claim language `midSoundnessLanguage` — only with **Schwartz–Zippel
> probability** `≤ natDegree (grandSumCheckPoly oStmt) / |F|`.

## What is proved fully here (no `sorry`, no named hypothesis)

* `Logup.midSoundnessLanguage` — the *genuine* intermediate language: the after-outer statements
  whose grand-sum check polynomial vanishes at the sampled challenge `x = stmt.xChallenge`, i.e. the
  lookup *appears valid* for that intermediate state. This is non-degenerate: it is **not**
  `Set.univ`; for a bad lookup it is hit only on the (few) roots of a nonzero polynomial.
* `Logup.prob_grandSumCheckPoly_root_le` — single-variable Schwartz–Zippel: for *any* nonzero
  `p : F[X]`, `Pr_{x ←$ᵖ F}[ p.eval x = 0 ] ≤ natDegree p / |F|`. Proved from Mathlib's
  `Polynomial.card_roots'` exactly as the in-tree weakened-KState bridge does.
* `Logup.grandSumCheckPoly_natDegree_le` — the degree of the check polynomial is `≤ |F| - 1`
  (every product summand ranges over `univ.erase a`, of size `|F| - 1`), giving a *uniform*
  closed-form SZ error.
* `Logup.outerSoundness_real` — the headline: for a bad input, the probability that a uniformly
  sampled outer challenge lands the check in `midSoundnessLanguage` (claim *appears* true) is at
  most `natDegree (grandSumCheckPoly oStmt) / |F| ≤ (|F| - 1) / |F|`. This is the **true** outer
  soundness bound the degenerate residual should have asked for.

## The one genuine residual (a named hypothesis, not a `sorry`)

Connecting this challenge-level SZ bound to the *protocol-level* `OuterSoundnessResidual`
(`(outerVerifier …).soundness …`) requires unfolding `Reduction.run` of the outer phase to show that
the after-outer statement's `xChallenge` field *is* the uniformly sampled outer challenge and that
the verifier's acceptance event coincides with the check-vanishing event. That `simulateQ`/`run`
unfolding (the prover-run composition side) is the deep monad-plumbing wall flagged throughout
`Security/**`; it is taken here as the explicit, clearly-named hypothesis
`OuterRunSamplesChallenge` of `Logup.outerSoundnessResidual_real_of_runUnfolding`. Everything *else*
— the Schwartz–Zippel mathematics that makes the bound true — is closed unconditionally above.
-/

open scoped NNReal ENNReal
open Polynomial Finset ProbabilityTheory

namespace Logup

section OuterSoundnessReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-! ### Single-variable Schwartz–Zippel for the grand-sum check polynomial -/

/-- **Univariate Schwartz–Zippel (root probability).** For a *nonzero* polynomial `p : F[X]`, a
uniformly sampled challenge `x` is a root of `p` with probability at most `natDegree p / |F|`.

Proved exactly as the in-tree weakened-KState bridge (`KStateWeaken.prob_badPolyAgreement_le`): the
root set has cardinality at most `natDegree p` by `Polynomial.card_roots'`, and uniform sampling
turns that count into the probability `(#roots)/|F| ≤ natDegree p / |F|`. -/
theorem prob_grandSumCheckPoly_root_le (p : F[X]) (hp : p ≠ 0) :
    Pr_{ let x ←$ᵖ F }[ p.eval x = 0 ] ≤ (p.natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  -- The root set is contained in `p.roots.toFinset`, of size `≤ natDegree p`.
  have hsub :
      (Finset.univ.filter (fun x : F => p.eval x = 0)) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hx.2)
  have hcard :
      (Finset.univ.filter (fun x : F => p.eval x = 0)).card ≤ p.natDegree :=
    calc (Finset.univ.filter (fun x : F => p.eval x = 0)).card
        ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
      _ ≤ p.natDegree := Polynomial.card_roots' p
  have hnum :
      ((Finset.univ.filter (fun x : F => p.eval x = 0)).card : ℝ≥0) ≤ (p.natDegree : ℝ≥0) := by
    exact_mod_cast hcard
  gcongr

/-- The grand-sum check polynomial has degree `≤ |F| - 1`: every summand is
`C (coeff) * ∏_{b ∈ univ.erase a} (X + C b)`, a product of `|F| - 1` monic linear factors, hence of
degree at most `|F| - 1`. This gives a *uniform* (input-independent) Schwartz–Zippel error. -/
theorem grandSumCheckPoly_natDegree_le (oStmt : ∀ i, OStmtIn F n M i) :
    (grandSumCheckPoly oStmt).natDegree ≤ Fintype.card F - 1 := by
  classical
  unfold grandSumCheckPoly
  refine Polynomial.natDegree_sum_le_of_forall_le (S := F) (s := Finset.univ)
    (f := fun a : F => Polynomial.C (if tableMultiplicityCount oStmt a = 0
        then (lookupMultiplicityCount oStmt a : F) else 0) *
      ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b)) ?_
  intro a _
  -- bound the degree of one summand `C c * ∏_{b ∈ erase a}(X + C b)`
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  -- each factor `X + C b` has degree ≤ 1
  have hfac : ∀ b ∈ Finset.univ.erase a,
      (Polynomial.X + Polynomial.C b : F[X]).natDegree ≤ 1 := by
    intro b _
    exact le_trans (Polynomial.natDegree_add_le _ _)
      (by simp [Polynomial.natDegree_X, Polynomial.natDegree_C])
  calc (∑ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b : F[X]).natDegree)
      ≤ ∑ _b ∈ Finset.univ.erase a, 1 := Finset.sum_le_sum hfac
    _ = (Finset.univ.erase a).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ = Fintype.card F - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

/-! ### The genuine intermediate "claim is true" language -/

/-- **The genuine soundness intermediate language.** A pair `(stmt, oStmt)` of an after-outer
statement and its oracle statements is in `midSoundnessLanguage` when the cleared grand-sum check
polynomial vanishes at the *outer challenge carried by `stmt`*, i.e. `grandSumCheckPoly oStmt`
evaluated at `stmt.xChallenge` is `0`. This is the genuine claim relation — "the lookup *appears*
valid for this intermediate state" — and, unlike the degenerate `midLanguage`, it is **not**
`Set.univ`: for a bad lookup `grandSumCheckPoly oStmt ≠ 0`, so membership pins `stmt.xChallenge`
to one of the finitely many roots of a nonzero polynomial. -/
def midSoundnessLanguage (oStmt : ∀ i, OStmtIn F n M i) : Set F :=
  { x : F | (grandSumCheckPoly oStmt).eval x = 0 }

/-- For a *bad* lookup the genuine intermediate language is **proper** (not all of `F`): there is a
challenge value at which the check polynomial does not vanish. This certifies that
`midSoundnessLanguage` is non-degenerate — the corrected statement is not vacuous. -/
theorem midSoundnessLanguage_ne_univ_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    midSoundnessLanguage oStmt ≠ Set.univ := by
  intro huniv
  -- if `midSoundnessLanguage = univ` then `grandSumCheckPoly` vanishes everywhere
  have hzero : ∀ x : F, (grandSumCheckPoly oStmt).eval x = 0 := by
    intro x
    have : x ∈ midSoundnessLanguage oStmt := by rw [huniv]; trivial
    exact this
  -- a nonzero polynomial has only finitely many roots; `grandSumCheckPoly ≠ 0` for a bad lookup,
  -- so it cannot vanish at *every* point unless the field is finite and small — but we get a
  -- direct contradiction via the proven nonvanishing-at-`-a₀` evaluation inside the converse lemma.
  have hne := grandSumCheckPoly_ne_zero_of_bad_lookup stmt oStmt hBad
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  -- evaluate at `-a₀`; the converse lemma's computation shows this is nonzero
  have heval := hzero (-a₀)
  rw [eval_grandSumCheckPoly] at heval
  -- reuse the exact vanishing argument: only the `a₀` summand survives
  have hterms : ∀ a ∈ (Finset.univ : Finset F), a ≠ a₀ →
      (if tableMultiplicityCount oStmt a = 0 then (lookupMultiplicityCount oStmt a : F) else 0) *
        ∏ b ∈ Finset.univ.erase a, (-a₀ + b) = 0 := by
    intro a _ hane
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hane, Finset.mem_univ a₀⟩)
        (neg_add_cancel a₀))
  rw [Finset.sum_eq_single a₀ hterms (fun hni => absurd (Finset.mem_univ a₀) hni)] at heval
  rw [if_pos htab] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

/-! ### The corrected outer soundness theorem -/

/-- **Corrected outer soundness (challenge level).** For a **bad** lookup input
(`∉ inputRelation`), a uniformly sampled outer challenge `x` lands in the genuine claim language
`midSoundnessLanguage oStmt` — i.e. makes the cleared grand-sum check *appear to pass* — with
probability at most the Schwartz–Zippel error `natDegree (grandSumCheckPoly oStmt) / |F|`.

This is the **non-degenerate replacement** for `OuterSoundnessResidual`: the soundness obstruction
is the algebraic check polynomial vanishing at the random challenge, and a bad lookup makes it
nonzero (`grandSumCheckPoly_ne_zero_of_bad_lookup`), so it vanishes only on its `≤ natDegree`
roots. -/
theorem outerSoundness_real
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]
      ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  have hne := grandSumCheckPoly_ne_zero_of_bad_lookup stmt oStmt hBad
  -- membership in `midSoundnessLanguage x` is *definitionally* the root event `eval x = 0`, so the
  -- two `Pr_{…}[…]` expressions coincide and the univariate SZ bound applies directly.
  show Pr_{ let x ←$ᵖ F }[ (grandSumCheckPoly oStmt).eval x = 0 ]
      ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0)
  exact prob_grandSumCheckPoly_root_le (grandSumCheckPoly oStmt) hne

/-- **Corrected outer soundness with the uniform closed-form error.** The same statement with the
input-independent Schwartz–Zippel error `(|F| - 1) / |F|` obtained from
`grandSumCheckPoly_natDegree_le`. This is the cleanest paper-shaped outer soundness bound: a bad
lookup passes the outer algebraic check at a random challenge with probability `≤ (|F| - 1)/|F|`,
strictly less than `1` whenever `F` is nontrivial. -/
theorem outerSoundness_real_uniformError
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  refine le_trans (outerSoundness_real stmt oStmt hBad) ?_
  gcongr
  · exact_mod_cast Nat.cast_le.mpr (grandSumCheckPoly_natDegree_le oStmt)

/-! ### Bridging to the protocol-level residual: the one named run-unfolding gap -/

/-- **The genuine residual interface: the outer run samples the challenge.** This is the *only* gap
between the proven challenge-level Schwartz–Zippel bound and a protocol-level outer-soundness
statement: it asserts that the outer verifier's acceptance probability for a bad input — landing the
after-outer statement in the *genuine* claim language — is bounded by the same uniform-challenge
event probability `Pr_{x ←$ᵖ F}[ x ∈ midSoundnessLanguage oStmt ]`. Discharging it requires unfolding
`Reduction.run` of the outer phase (the prover-run composition side: the after-outer `xChallenge` is
the uniformly sampled outer challenge, and the verifier accepts iff the check vanishes). That is the
deep `simulateQ`/`run` monad-plumbing wall flagged throughout `Security/**`; it is kept here as an
explicit, clearly-named hypothesis rather than hidden behind `sorryAx`. -/
def OuterRunSamplesChallenge
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (outerBadAcceptProb : ℝ≥0∞) : Prop :=
  outerBadAcceptProb ≤ Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]

/-- **Protocol-level corrected outer soundness, modulo the run-unfolding residual.** Given the named
run-unfolding bridge `OuterRunSamplesChallenge` (the after-outer challenge is the uniformly sampled
outer challenge and acceptance is the check-vanishing event), the outer phase maps a bad lookup into
the genuine claim language with probability bounded by the Schwartz–Zippel error. The mathematics is
discharged unconditionally by `outerSoundness_real`; only the monad-plumbing bridge is assumed. -/
theorem outerSoundnessResidual_real_of_runUnfolding
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (outerBadAcceptProb : ℝ≥0∞)
    (hRun : OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb) :
    outerBadAcceptProb ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) :=
  le_trans hRun (outerSoundness_real stmt oStmt hBad)

end OuterSoundnessReal

end Logup

/- Axiom audit for the corrected #13 outer-soundness bricks. -/
#print axioms Logup.prob_grandSumCheckPoly_root_le
#print axioms Logup.grandSumCheckPoly_natDegree_le
#print axioms Logup.midSoundnessLanguage_ne_univ_of_bad_lookup
#print axioms Logup.outerSoundness_real
#print axioms Logup.outerSoundness_real_uniformError
#print axioms Logup.outerSoundnessResidual_real_of_runUnfolding
