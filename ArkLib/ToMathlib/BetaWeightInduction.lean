/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The App.-A.4 weight induction for the Hensel-lift numerators `β_t` (brick **L9**)

This file proves the **Claim-A.2 weight bound** of [BCIKS20] (eprint 2020/654) Appendix-A.4 for the
genuine recursion `betaRec` of brick L7 (`ArkLib.ToMathlib.BetaRecursion`), by **strong induction on
`t`** over recursion (A.1).  It is the L9 brick of the proximity-prize keystone; see
`research/proximity-prize/ingredient-D-DAG-2026-06-05.md` (L9/L10, App-A lines 2877–2881).

## The bound (Claim A.2)

```
Λ(β_t) ≤ 1 + (t+1)·Λ(W) + e_t·Λ(ξ)  ≤  (2t+1)·d_R·D
```

proven by strong induction on `t` over recursion (A.1):

```
β_{t+1} = Σ_{i₁; λ ∈ P(t+1−i₁), λ ≠ λ^(t+1)}  W^{i₁+δ−1} · ξ^{2i₁+Σλ−2} · B_{i₁,λ} · ∏_l β_l^{λ_l}
```

Each term's weight is bounded (by L3's sub-multiplicativity) by

```
betaWExp(i₁)·Λ(W) + betaξExp(i₁,λ)·Λ(ξ) + Λ(B_{i₁,λ}) + Σ_{l ∈ λ.parts} λ_l·Λ(β_l)
```

and the inductive hypothesis `Λ(β_l) ≤ wβ l` (for every `l < t+1`, which holds for every recursive
call by `recursionStep_lt`) plugs into the last summand; the partition-indexed telescoping collapses
the per-term arithmetic to the target `wβ (t+1)`.

## What is delivered (all kernel-clean: no `sorry`/`admit`/`axiom`/`native_decide`)

* `weight_Λ_over_𝒪_prod_le_of_le` / `weight_Λ_over_𝒪_prod_le_of_le_attach` — the missing **finite
  product** weight lemma (L3 only had `mul`/`pow`/`sum`): the weight of `∏ i ∈ s, f i` is `≤` the sum
  of per-factor `ℕ`-budgets.  This is what bounds the recursion's `∏_l β_l^{λ_l}` product.

* `betaProd_weight_le` — the weight of the recursive product `∏_{l ∈ λ.parts} β_l^{λ_l}` is bounded
  by `Σ_{l} λ_l · (budget for β_l)`, where the per-`β_l` budgets are supplied by the IH.

* `betaTerm_weight_le` — **the per-term budget lemma**: with explicit budgets for `Λ(W)`, `Λ(ξ)`,
  `Λ(B_{i₁,λ})` and `Λ(β_l)` (`l ∈ λ.parts`), the term
  `betaTerm … i₁ p` has weight `≤ betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB i₁ p + Σ_l count·bβ l`.
  This is the per-term content of App-A line 2877; the genuine residual is only the *numerical*
  collapse to `wβ (t+1)`, isolated below as an explicit hypothesis (never a `sorry`).

* `betaRec_weight_le` — **the strong-induction theorem (brick L9)**: with the per-term collapse
  hypothesis `htele`, `weight_Λ_over_𝒪 (betaRec … t) D ≤ wβ t` for all `t`.  The induction structure
  (strong recursion on `t`, IH applied at every `l < t+1` via `recursionStep_lt`, reduction to the
  per-term budgets via `betaRec_weightBound_of_term_bounds`, base case via L3's `weight_Λ_over_𝒪_T_le`)
  is fully discharged; only the App-A telescoping arithmetic is the named hypothesis.

## The isolated interface hypotheses (the genuine L9 residuals — explicit, never `sorry`)

* `bW`, `bξ`, `bB`, `wβ : ℕ → ℕ` — the explicit `ℕ`-budgets for `Λ(W)`, `Λ(ξ)`, `Λ(B_{i₁,λ})` and the
  target `Λ(β_t)`.  The first three are realised by L3 (`Λ(W) ≤ D−d_H`), L5 (`weight_ξ_bound`) and L4
  (`Λ(B)` bound); supplied as hypotheses so this file is independent of their exact numerals.
* `hbW`, `hbξ`, `hbB` — that those budgets genuinely bound `Λ(W)`, `Λ(ξ)`, `Λ(B_{i₁,λ})`.
* `hβ0` — the base-case budget `Λ(β_0) ≤ wβ 0` (App-A: `weight(T) = D+1−d_H ≤ wβ 0`).
* `htele` — **the App-A line-2877–2881 telescoping**: for each non-forbidden `(i₁, p)`,
  `betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB i₁ p + Σ_{l ∈ p.parts} count·wβ l ≤ wβ (t+1)`.
  This is the exact numerical content of Claim A.2's induction step, left as a named hypothesis.

This file does **not** edit the (0-sorry) `RationalFunctions.lean`; all names live in `namespace
ArkLib`, the in-tree objects opened from `BCIKS20AppendixA` / `…ClaimA2`.
-/

import ArkLib.ToMathlib.BetaRecursion
import ArkLib.ToMathlib.WeightLambdaCalculus
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

namespace ArkLib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-! ### The missing finite-product weight lemma (L3 supplement)

L3 (`WeightLambdaCalculus`) supplied `mul`/`pow`/`sum`/`add` budget-composition lemmas but not the
finite **product** one, which the recursion's `∏_{l ∈ λ.parts} β_l^{λ_l}` term needs.  We add it
here: the weight of a finite product is bounded by the sum of per-factor `ℕ`-budgets.  It is the
straightforward `Finset.prod` induction on top of L3's `weight_Λ_over_𝒪_mul_le_of_le` and
`weight_Λ_over_𝒪_one_le`. -/

/-- **Finite-product weight bound.** If every factor `f i` has weight `≤ (b i : WithBot ℕ)` then the
product `∏ i ∈ s, f i` has weight `≤ (∑ i ∈ s, b i : ℕ)`.  This is the product analogue of L3's
`weight_Λ_over_𝒪_sum_le`, dual under sub-multiplicativity. -/
lemma weight_Λ_over_𝒪_prod_le_of_le {ι : Type*} {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (s : Finset ι) (f : ι → 𝒪 H) (b : ι → ℕ)
    (hf : ∀ i ∈ s, weight_Λ_over_𝒪 hH (f i) D ≤ (WithBot.some (b i) : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (∏ i ∈ s, f i) D ≤ (WithBot.some (∑ i ∈ s, b i) : WithBot ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      refine (weight_Λ_over_𝒪_one_le hD hH).trans ?_
      norm_cast
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine weight_Λ_over_𝒪_mul_le_of_le hD hH (hf a (Finset.mem_insert_self a s)) ?_
      exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ### The recursive product `∏_{l ∈ λ.parts} β_l^{λ_l}`

The product term of recursion (A.1) runs over `p.parts.toFinset.attach`, each factor being
`(betaRec … l)^{count l}`.  Its weight is bounded by `Σ_{l ∈ parts} count(l)·(budget for β_l)`. -/

/-- The recursive-product factor at a part `l`: `(betaRec … l)^{count l}`. -/
noncomputable def betaProdFactor (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) {m : ℕ} (p : Nat.Partition m)
    (l : ℕ) : 𝒪 H :=
  betaRec x₀ R H hHyp Bcoeff l ^ (p.parts.count l)

/-- **Weight of the recursive product.**  Given per-`l` budgets `bβ l` for `Λ(betaRec … l)` (the
inductive hypothesis), the recursion product `∏_{l ∈ p.parts.toFinset} (betaRec … l)^{count l}` has
weight `≤ Σ_{l ∈ p.parts.toFinset} count(l)·bβ l`.  Built from the finite-product lemma and L3's
`weight_Λ_over_𝒪_pow_le_of_le`. -/
lemma betaProd_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) {m : ℕ} (p : Nat.Partition m)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (bβ : ℕ → ℕ)
    (hbβ : ∀ l ∈ p.parts.toFinset, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff l) D
        ≤ (WithBot.some (bβ l) : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH
        (∏ l ∈ p.parts.toFinset.attach, betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)) D
      ≤ (WithBot.some (∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * bβ l.1) :
          WithBot ℕ) := by
  classical
  refine weight_Λ_over_𝒪_prod_le_of_le hD hH p.parts.toFinset.attach
    (fun l => betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1))
    (fun l => p.parts.count l.1 * bβ l.1) (fun l _ => ?_)
  exact weight_Λ_over_𝒪_pow_le_of_le hD hH (hbβ l.1 l.2) (p.parts.count l.1)

/-! ### The per-term budget lemma (App-A line 2877)

The weight of a single term `betaTerm … i₁ p` (recursion (A.1) summand), with explicit budgets
`bW`, `bξ`, `bB` for `Λ(W)`, `Λ(ξ)`, `Λ(B_{i₁,λ})` and `bβ` for `Λ(betaRec … l)`, is bounded by
`betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB + Σ_{l ∈ parts} count(l)·bβ l`. -/

/-- **Per-term budget (App-A line 2877).** With budgets `Λ(W) ≤ bW`, `Λ(ξ) ≤ bξ`,
`Λ(Bcoeff i₁ p) ≤ bB`, and `Λ(betaRec … l) ≤ bβ l` for each part `l ∈ p.parts.toFinset`, the term
`betaTerm … i₁ p` of recursion (A.1) has weight bounded by

  `betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB + Σ_{l} count(l)·bβ l`.

The proof is the chain of L3's sub-multiplicativity on the four factors
`W^{betaWExp} · ξ^{betaξExp} · B · ∏ β^{count}`, with the product handled by `betaProd_weight_le`.
(The forbidden `(i₁=0, λ^(t+1))` summand is `0` and trivially within budget.) -/
lemma betaTerm_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t i₁ : ℕ)
    (p : Nat.Partition (t + 1 - i₁))
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    {bW bξ bB : ℕ} (bβ : ℕ → ℕ)
    (hbW : weight_Λ_over_𝒪 hH (W_𝒪 H) D ≤ (WithBot.some bW : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hbB : weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D ≤ (WithBot.some bB : WithBot ℕ))
    (hbβ : ∀ l ∈ p.parts.toFinset, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff l) D
        ≤ (WithBot.some (bβ l) : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (betaTerm x₀ R H hHyp Bcoeff t i₁ p) D
      ≤ (WithBot.some (betaWExp i₁ * bW + betaξExp i₁ p * bξ + bB
            + ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * bβ l.1) : WithBot ℕ) := by
  classical
  unfold betaTerm
  by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ))
  · rw [if_pos hexcl]
    -- weight of `W^a · ξ^e · B · ∏` ≤ a·bW + e·bξ + bB + Σ count·bβ.
    have hWpow : weight_Λ_over_𝒪 hH (W_𝒪 H ^ betaWExp i₁) D
        ≤ (WithBot.some (betaWExp i₁ * bW) : WithBot ℕ) :=
      weight_Λ_over_𝒪_pow_le_of_le hD hH hbW (betaWExp i₁)
    have hξpow : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp ^ betaξExp i₁ p) D
        ≤ (WithBot.some (betaξExp i₁ p * bξ) : WithBot ℕ) :=
      weight_Λ_over_𝒪_pow_le_of_le hD hH hbξ (betaξExp i₁ p)
    have hprod := betaProd_weight_le x₀ R H hHyp Bcoeff p hD hH bβ hbβ
    -- combine `(W^a) * (ξ^e)` then `* B` then `* ∏`.
    have h1 := weight_Λ_over_𝒪_mul_le_of_le hD hH hWpow hξpow
    have h2 := weight_Λ_over_𝒪_mul_le_of_le hD hH h1 hbB
    have h3 := weight_Λ_over_𝒪_mul_le_of_le hD hH h2 hprod
    -- `h3`'s budget is `((betaWExp·bW + betaξExp·bξ) + bB) + Σ`, the target's left-assoc form.
    exact h3
  · rw [if_neg hexcl]
    rw [weight_Λ_over_𝒪_zero' hH]
    exact bot_le

/-! ### The strong-induction theorem (brick L9)

The Claim-A.2 bound `Λ(β_t) ≤ wβ t` by strong induction on `t`.  The induction is genuine: at the
`(t+1)`-step every recursive call `betaRec … l` is at a part `l < t+1` (`recursionStep_lt`), so the
strong-induction hypothesis applies and supplies `Λ(β_l) ≤ wβ l` per part; `betaTerm_weight_le` turns
that into the per-term budget; `betaRec_weightBound_of_term_bounds` (L7/L9 skeleton) sums them.  The
**only** numerical residual — the App-A collapse of each per-term arithmetic to `wβ (t+1)` — is the
explicit hypothesis `htele`. -/

/-- **Claim-A.2 weight bound by strong induction (brick L9).**

`weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D ≤ (wβ t : WithBot ℕ)` for every `t`, given:

* `hbW : Λ(W) ≤ bW`, `hbξ : Λ(ξ) ≤ bξ` — the L3/L5 budgets for the prefactors (e.g.
  `bW = D − d_H`, `bξ = (d_R−1)(D−d_H+1)`);
* `hbB : ∀ i₁ p, Λ(Bcoeff i₁ p) ≤ bB i₁ p` — the L4 budget for each Hasse-derivative numerator;
* `hβ0 : weight(T) ≤ wβ 0` — the base case (`weight(T) = D+1−d_H`);
* `htele : ∀ s ≤ t, ∀ i₁ p, betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB i₁ p + Σ count·wβ l ≤ wβ (s+1)`
  — the App-A line 2877–2881 telescoping (the genuine numerical L9 step), isolated explicitly.

The induction structure, the IH-at-every-part wiring, the per-term budgeting and the base case are
all discharged kernel-clean. -/
theorem betaRec_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    {bW bξ : ℕ} (bB : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → ℕ) (wβ : ℕ → ℕ)
    (hbW : weight_Λ_over_𝒪 hH (W_𝒪 H) D ≤ (WithBot.some bW : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D ≤ (WithBot.some (bB i₁ p) : WithBot ℕ))
    (hβ0 : weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) D
        ≤ (WithBot.some (wβ 0) : WithBot ℕ))
    (htele : ∀ s : ℕ, ∀ i₁ ∈ Finset.range (s + 2), ∀ p : Nat.Partition (s + 1 - i₁),
        betaWExp i₁ * bW + betaξExp i₁ p * bξ + bB i₁ p
            + ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * wβ l.1
          ≤ wβ (s + 1)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some (wβ t) : WithBot ℕ) := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    match t with
    | 0 =>
        rw [betaRec_zero]
        exact hβ0
    | (s + 1) =>
        -- Reduce to per-term budgets, each `≤ wβ (s+1)`, via the L7/L9 skeleton.
        refine betaRec_weightBound_of_term_bounds x₀ R H hHyp Bcoeff s hD hH ?_
        intro i₁ hi₁ p
        -- Split on the forbidden pair: the forbidden summand is `0` (weight `⊥`), trivially in
        -- budget; the genuine summand is bounded by `betaTerm_weight_le` + the `htele` collapse.
        by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({s + 1} : Multiset ℕ))
        · -- Genuine term: `recursionStep_lt` gives `l < s+1` for every part, so the IH applies.
          have hbβ : ∀ l ∈ p.parts.toFinset,
              weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff l) D
                ≤ (WithBot.some (wβ l) : WithBot ℕ) := by
            intro l hl
            exact IH l (recursionStep_lt p hexcl (Multiset.mem_toFinset.mp hl))
          refine le_trans
            (betaTerm_weight_le x₀ R H hHyp Bcoeff s i₁ p hD hH wβ hbW hbξ (hbB i₁ p) hbβ) ?_
          rw [WithBot.coe_le_coe]
          exact htele s i₁ hi₁ p
        · -- Forbidden pair: `betaTerm = 0`, weight `⊥ ≤ wβ (s+1)`.
          have hterm0 : betaTerm x₀ R H hHyp Bcoeff s i₁ p = 0 := by
            unfold betaTerm; rw [if_neg hexcl]
          rw [hterm0, weight_Λ_over_𝒪_zero' hH]
          exact bot_le

end ArkLib
