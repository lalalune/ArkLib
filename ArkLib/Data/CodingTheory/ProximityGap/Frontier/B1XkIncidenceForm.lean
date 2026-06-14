/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Issue407SaturatedIncidence

/-!
# B1: the `x^k` far-direction divided-difference ratio form (#407, B-count lane)

## What this file records

For RS over the `n`-th roots of unity `μ_n`, the *far-line incidence* (the EXACT `δ*`
object, `FarCosetExplosion.epsMCA_ge_far_incidence`) at the deepest scale `size = k+1`
is governed by the *divided-difference ratios*

`lambda_R(x^a) / lambda_R(x^k)`

over `(k+1)`-subsets `R ⊆ μ_n`.  The in-tree `dividedDifferencePow` is exactly
`lambda_R(x^a)`, and `completeHomReadout R v j = h_j(R) = lambda_R(x^{|R|-1+j})`
(see `_CompleteHomogeneousReadout.lean`).  Because `lambda_R(x^k) = h_0(R) = 1` for a
`(k+1)`-set, the ratio is just `h_{a-k}(R)`.

## The provable mechanism (this file proves it)

The cyclic group `Z_n` acts on `μ_n` by `z ↦ w·z` (`w` a primitive `n`-th root).  Under a
GLOBAL rescaling of every node by a scalar `c`, the readout transforms covariantly:

`completeHomReadout_smul : h_j(c • v) = c^j · h_j(v)`              (PROVED here)
`dividedDifferencePow_smul : [s](c•v) x^b = c^{b-(#s-1)} · [s]v x^b`   (PROVED here)

This is the engine behind the empirical count law below: rotating `R` by `w` multiplies
`h_{n-1-k}(R)` by `w^{n-1-k} = w^{-(k+1)}`, so the value set is closed under multiplication
by `w^{-(k+1)}`, with no value ever `0`.

## The empirical closed form (stated, NOT proved — named open Props)

Exhaustive enumeration (`probe_farline_incidence_exact`, p-independent across primes
`p ≡ 1 mod n`, verified `n ∈ {7,8,9,11,12,16,20,32}`, all `1 ≤ k ≤ n-2`, ρ ∈ {1/4,1/2,…})
established:

* **TOP direction `a = n-1`** (value `h_{n-1-k}(R)`): the number of DISTINCT ratios is
  **exactly `n`**, p-independent and k-independent.  When `gcd(n,k+1)=1` the `n` fibers are
  PERFECTLY balanced of size `C(n,k+1)/n` (the `Z_n` action on `(k+1)`-subsets is free).
* **Full ratio-vector** `(h_0,…,h_{n-1-k})(R)` is INJECTIVE in `R` (count `= C(n,k+1)`).
* **Bottom direction `a = k`** (`h_0`): the ratio is constant `= 1`.
* **The intermediate counts are NOT a function of `gcd(n,a-k)` alone** (refuted:
  `n=16`, `d=4` gives `713`, `d=8` gives `428` — both gcd-positive, values differ), so there
  is no clean single-direction closed form except at the two boundaries `a=k` (`=1`) and
  `a=n-1` (`=n`).

These are recorded as `Prop`s; no theorem here claims to prove the count law.

NUMERIC ANCHOR connecting to `δ*`: at the binding scale `size = k+1` (deepest `r = n-k-1`),
`max_far_incidence` equals exactly `n` at the threshold (`n=8,k=2`: `inc=8`; `n=12,k=3`:
`inc=12`), reproducing `δ*(8,2)=3/8`, `δ*(12,3)=5/12` — the established session values.
-/

namespace ProximityGap.Frontier.B1XkIncidenceForm

open Finset
open ProximityGap.SchurLagrange

variable {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]

/-- **Rescaling covariance of the raw divided difference** (the B1 engine).
Globally scaling every node value by `c ≠ 0` multiplies each summand `[term_i]` of `[s] x^b` by
`c^b · (c^{#(s.erase i)})⁻¹ = c^b · (c^{#s-1})⁻¹`.  We state the per-term identity, which is the
content; the global power factor `c^{b-(#s-1)}` then factors out by `Finset.sum`-congruence. -/
theorem dividedDifferencePow_smul_term (s : Finset ι) (v : ι → F) (b : ℕ) (i : ι)
    (hi : i ∈ s) {c : F} (hc : c ≠ 0) :
    (c * v i) ^ b * (∏ j ∈ s.erase i, (c * v i - c * v j))⁻¹
      = c ^ b * (c ^ (#s - 1))⁻¹ * ((v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
  classical
  have hcard : #(s.erase i) = #s - 1 := Finset.card_erase_of_mem hi
  have hprod : (∏ j ∈ s.erase i, (c * v i - c * v j))
      = c ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    ring
  rw [hprod, mul_pow, mul_inv]
  ring

/-- **Global rescaling covariance of the raw divided difference.**
`[s] (c•v) x^b = c^b · (c^{#s-1})⁻¹ · [s] v x^b`, which equals `c^{b-(#s-1)} · [s]v x^b` when
`b ≥ #s-1`.  Assembles `dividedDifferencePow_smul_term` over the sum. -/
theorem dividedDifferencePow_smul (s : Finset ι) (v : ι → F) (b : ℕ) {c : F} (hc : c ≠ 0) :
    dividedDifferencePow s (fun i => c * v i) b
      = c ^ b * (c ^ (#s - 1))⁻¹ * dividedDifferencePow s v b := by
  classical
  unfold dividedDifferencePow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact dividedDifferencePow_smul_term s v b i hi hc

/-- Local complete-homogeneous readout `h_j(R) = λ_R(x^{|R|-1+j})` (= `dividedDifferencePow` at
shifted exponent), self-contained to avoid the absent Frontier scaffold. -/
noncomputable def completeHomReadout (s : Finset ι) (v : ι → F) (j : ℕ) : F :=
  dividedDifferencePow s v (#s - 1 + j)

/-- **Readout covariance.** Globally scaling every node by `c ≠ 0` multiplies the
complete-homogeneous readout `h_j` by `c^j`: `h_j(c • v) = c^j h_j(v)`.
(Verified numerically for all sampled `j, c`.)  This is the engine behind the top-direction
count law: rotating `μ_n` by a primitive root `w` sends `h_j ↦ w^j h_j`. -/
theorem completeHomReadout_smul (s : Finset ι) (v : ι → F) (j : ℕ) {c : F} (hc : c ≠ 0)
    (hs : s.Nonempty) :
    completeHomReadout s (fun i => c * v i) j
      = c ^ j * completeHomReadout s v j := by
  classical
  unfold completeHomReadout
  rw [dividedDifferencePow_smul s v (#s - 1 + j) hc]
  have hpos : 1 ≤ #s := Finset.card_pos.mpr hs
  have hpow : c ^ (#s - 1 + j) * (c ^ (#s - 1))⁻¹ = c ^ j := by
    rw [pow_add, mul_comm (c ^ (#s - 1)) (c ^ j), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hc), mul_one]
  rw [mul_assoc, ← mul_assoc (c ^ (#s - 1 + j)), hpow]

/-- The set of distinct top-direction ratios `h_{n-1-k}(R)` over all `(k+1)`-subsets `R` of a
node set `nodes : Finset ι` with `v` injective.  Abstractly: the image of
`R ↦ completeHomReadout R v (n-1-k)` over `(k+1)`-subsets. -/
noncomputable def topRatioValues (nodes : Finset ι) (v : ι → F) (n k : ℕ) : Finset F :=
  (nodes.powersetCard (k + 1)).image
    (fun R => completeHomReadout R v (n - 1 - k))

/-- **B1 TOP-DIRECTION COUNT LAW (named OPEN Prop).** For `μ_n` (the `n`-th roots of unity,
`#nodes = n`, `v` the inclusion), the number of distinct top-direction divided-difference
ratios `h_{n-1-k}(R)` over `(k+1)`-subsets is exactly `n`, for every `1 ≤ k ≤ n-2`.

p-independent; verified exhaustively for `n ∈ {7,8,9,11,12,16,20,32}`.  NOT proved here. -/
def TopDirectionDistinctCountEqN : Prop :=
  ∀ (nodes : Finset ι) (v : ι → F) (n k : ℕ),
    nodes.card = n → 1 ≤ k → k ≤ n - 2 → Set.InjOn v ↑nodes →
    -- (μ_n hypothesis would be added: v ''nodes = n-th roots of unity)
    (topRatioValues nodes v n k).card = n

/-- **B1 BALANCED-FIBER Prop (named OPEN, the `gcd=1` refinement).** When `gcd(n,k+1)=1`, the
`Z_n` rotation action on `(k+1)`-subsets is free, so each of the `n` top-direction value-fibers
has size exactly `C(n,k+1)/n`.  Stated abstractly as: the fibers all share one cardinality.
Verified for all `gcd(n,k+1)=1` rows in the enumeration. NOT proved here. -/
def TopDirectionBalancedFibers : Prop :=
  ∀ (nodes : Finset ι) (v : ι → F) (n k : ℕ),
    nodes.card = n → 1 ≤ k → k ≤ n - 2 → Nat.gcd n (k + 1) = 1 → Set.InjOn v ↑nodes →
    ∀ w ∈ topRatioValues nodes v n k,
      ((nodes.powersetCard (k + 1)).filter
        (fun R => completeHomReadout R v (n - 1 - k) = w)).card
        * n = (nodes.card.choose (k + 1))

/- **REFUTED sub-claim (numeric, not a Lean theorem).** The intermediate-direction
distinct count is NOT a function of `gcd(n, a-k)` alone.  Concretely at `n=16`: direction
`d=4` (`gcd=4`) gives `713` distinct values while `d=8` (`gcd=8`) gives `428`, and BOTH differ
from a pure-gcd prediction.  We record only that no `gcd`-only law exists; the witness lives in
`probe_farline_incidence_exact` output, not in Lean. -/
-- (no Lean Prop; the gcd-only law is refuted numerically: n=16 d=4->713 vs d=8->428)

end ProximityGap.Frontier.B1XkIncidenceForm

#print axioms ProximityGap.Frontier.B1XkIncidenceForm.dividedDifferencePow_smul
#print axioms ProximityGap.Frontier.B1XkIncidenceForm.completeHomReadout_smul
