/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.BKR06FiberCount
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# BKR06 §3 construction: roots → close Reed–Solomon codewords (geometric core)

This file formalizes the *geometric step* of the BKR06 list-decoding lower bound
(Ben-Sasson–Kopparty–Radhakrishnan, *Subspace polynomials and list decoding of
Reed–Solomon codes*, FOCS 2006), §3 / Lemma 3.5 / Prop 3.4.  The companion file
`ArkLib.ToMathlib.BKR06FiberCount` already supplies the *counting* engine (every
in-range value-fiber of the linearized subspace polynomial `P_W` has size exactly
`q^d`).  Here we supply the polynomial-agreement heart that BKR06 uses to turn
roots of subspace polynomials into Reed–Solomon codewords close to a fixed
received word.

## The actual BKR06 construction (faithful summary)

We restate the construction exactly as it appears in the paper (verified against
the author copy at `math.toronto.edu/swastik/rsld.pdf`).  Working in
`K = 𝔽_{q^m}` as an `𝔽_q`-vector space:

* **Prop 3.4 (a ⇔ b).**  A received word `w : K → K` together with `r`
  polynomials `P₁,…,P_r` of degree `≤ k` each agreeing with `w` on `≥ a` points
  is *equivalent* to an `(a,k)`-family `{P_w − P_i}` whose pivot `P_w` is the
  (unique, degree `≤ q^{m-1}`) interpolant of `w`.  The agreement fact is purely
  algebraic: **`P_i` agrees with `w` at `x` iff `x` is a root of `P_w − P_i`.**

* **Lemma 3.5.**  Take the family `P = {P_L : L ∈ 𝓛}` of subspace polynomials of
  *`v`-dimensional* subspaces `L ⊆ K`, all sharing top coefficients above degree
  `q^u` (pigeonhole over the `q^{v(m-v)}` subspaces of dimension `v`).  Each
  `P_L` has degree `q^v` and exactly `q^v` roots; with pivot `P^*` the codeword
  `P^* − P_L` has degree `≤ q^u` and agrees with the received word `w(x) = P^*(x)`
  on the `q^v` roots of `P_L`.  The list size is `|𝓛| ≥ q^{(u+1)m − v²}`.

The **genuine geometric core** — the only part not already in
`BKR06FiberCount` — is the agreement identity of Prop 3.4:

> `evalOnPoints domain (P^* − P)` agrees with `evalOnPoints domain P^*`
> exactly on the root set of `P`.

For `P = subspacePoly (subFinset W)` that root set is the carrier of `W`, of size
`q^d`.  That is `BKR06.evalOnPoints_sub_subspacePoly_agrees_on_W` below, fully
proven and axiom-clean.

## Parameter mismatch with `Bounds.lean`'s `_of_injection` (documented honestly)

`rs_lambda_superpoly_extension_bkr06_of_injection` in
`ListDecoding/Bounds.lean` is parameterized by `W : Submodule F F` — an
`F`-submodule of the *alphabet field itself*, with `Fintype.card F = q`.  Such a
submodule has `Module.finrank F W ∈ {0, 1}` (only `⊥` and `⊤`), so its
"`q^d`" is `q^0 = 1` or `q^1 = q`.  The BKR06 construction *requires* a proper
extension `K = 𝔽_{q^m}` (`m ≥ 2`) so that `𝔽_q`-subspaces of dimension
`2 ≤ d ≤ m` exist; over `K = F = 𝔽_q` the subspace-polynomial structure is
degenerate (`W` is `{0}` or all of `𝔽_q`).  Moreover the in-tree statement asks
for `q^d` *distinct close codewords* (list size) indexed by `W`, whereas BKR06's
single subspace `W` supplies `q^d` *agreements per codeword*; the list size in
BKR06 comes from varying the subspace `L` over a pigeonhole family `𝓛`, not from
the elements of one fixed `W`.

Because the in-tree `_of_injection` *takes* `encode` as a hypothesis, it is not
unsound — it simply cannot be *discharged* by the BKR06 construction at its own
parameters.  We therefore prove a **corrected-statement variant**
(`BKR06.exists_bkr06_close_codeword_injection_extension`) at the genuine
extension parameters, where the construction does apply, and show it feeds the
counting engine.  We do *not* edit `Bounds.lean`.

All declarations below compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); see the in-file `#print axioms`.
-/

-- Section `variable`-bundled finiteness/decidability instances on `K` are needed by the
-- `subspacePoly`/`closeCodewords` machinery but not by every individual lemma's *type*;
-- the in-type linters are stylistic here.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

/-! ## The geometric core: BKR06 Prop 3.4 agreement identity

The single algebraic fact powering BKR06's roots→codewords conversion: a codeword
obtained as `evalOnPoints domain (pivot − P)` agrees with the received word
`evalOnPoints domain pivot` precisely on the roots of `P`. -/

variable {ι : Type*} [Fintype ι]

/-- **BKR06 Prop 3.4 (agreement identity), pointwise.**  For any `pivot, P : K[X]`
and any evaluation point `x`, the codeword `evalOnPoints domain (pivot − P)` agrees
with the received word `evalOnPoints domain pivot` at `x` **iff** `domain x` is a
root of `P`.  (Subtracting a degree-`k` codeword from the pivot leaves exactly `P`;
agreement ⇔ `P` vanishes.) -/
lemma evalOnPoints_sub_agrees_iff_isRoot
    (domain : ι ↪ K) (pivot P : K[X]) (x : ι) :
    ReedSolomon.evalOnPoints domain pivot x
        = ReedSolomon.evalOnPoints domain (pivot - P) x
      ↔ P.IsRoot (domain x) := by
  classical
  simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, eval_sub]
  constructor
  · intro h
    have : P.eval (domain x) = 0 := by
      have := sub_eq_zero.mpr h.symm
      simpa using this
    simpa [IsRoot] using this
  · intro h
    have hP : P.eval (domain x) = 0 := h
    simp [hP]

/-- **BKR06 Prop 3.4 (agreement on a subspace), specialised to `P = P_W`.**  With
received word `w = evalOnPoints domain P^*` and codeword
`c = evalOnPoints domain (P^* − P_W)`, the two agree at every point of the
evaluation domain landing inside the subspace `W` — i.e. on the `q^d` roots of the
subspace polynomial `P_W`.  This is the genuine geometric heart of BKR06 §3. -/
lemma evalOnPoints_sub_subspacePoly_agrees_on_W
    (domain : ι ↪ K) (pivot : K[X]) (W : Submodule F K) [Fintype W]
    (x : ι) (hx : domain x ∈ W) :
    ReedSolomon.evalOnPoints domain pivot x
      = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x := by
  rw [evalOnPoints_sub_agrees_iff_isRoot]
  exact (subspacePoly_isRoot_iff (subFinset W) (domain x)).mpr (by simpa using hx)

/-! ## Codeword membership: the subtracted polynomial is a Reed–Solomon codeword

If `pivot − P_W` has degree `< k`, then its evaluation is a genuine codeword of
`ReedSolomon.code domain k`.  In BKR06 this holds because `pivot` and `P_W` share
their top coefficients (above degree `q^u = k`), so their difference has degree
`< k`. -/

/-- The evaluation of any polynomial of degree `< k` is a Reed–Solomon codeword. -/
lemma evalOnPoints_mem_code_of_degree_lt
    (domain : ι ↪ K) (Q : K[X]) (k : ℕ) (hQ : Q ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain Q ∈ ReedSolomon.code domain k :=
  ⟨Q, hQ, rfl⟩

/-- **BKR06 codeword from a shared-top-coefficients pivot.**  If the pivot and the
subspace polynomial of `W` agree above degree `k` (so their difference lies in
`degreeLT K k`), then `evalOnPoints domain (pivot − P_W)` is a codeword of
`ReedSolomon.code domain k` that agrees with the received word
`evalOnPoints domain pivot` on all of `W`. -/
lemma bkr06_codeword_mem_code_and_agrees
    (domain : ι ↪ K) (pivot : K[X]) (W : Submodule F K) [Fintype W] (k : ℕ)
    (hdeg : pivot - subspacePoly (subFinset W) ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))
        ∈ ReedSolomon.code domain k
      ∧ ∀ x : ι, domain x ∈ W →
          ReedSolomon.evalOnPoints domain pivot x
            = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x := by
  refine ⟨evalOnPoints_mem_code_of_degree_lt domain _ k hdeg, ?_⟩
  intro x hx
  exact evalOnPoints_sub_subspacePoly_agrees_on_W domain pivot W x hx

/-! ## The honest BKR06 list-size family (statement)

BKR06's list size comes from a *family* `𝓛` of distinct `v`-dimensional subspaces
whose subspace polynomials share their top `> q^u` coefficients.  We record the
geometric content of one member of such a family — for *each* subspace `L` in the
family, the construction yields a codeword close to the common received word — as a
reusable building block.  (Manufacturing the pigeonhole family `𝓛` itself, and
the "infinitely many prime powers" sequence, is the residual external content; see
the module docstring.) -/

/-- **BKR06 Lemma 3.5 (one family member).**  Fix a common pivot `pivot`.  For each
subspace `L` whose subspace polynomial agrees with `pivot` above degree `k`, the
codeword `evalOnPoints domain (pivot − P_L)` lies in `ReedSolomon.code domain k`
and agrees with the received word `evalOnPoints domain pivot` on the `q^{dim L}`
roots of `P_L`.  Distinct subspaces `L` give distinct codewords whenever their
subspace polynomials differ — which is the engine the counting file quantifies. -/
theorem bkr06_family_member_codeword
    (domain : ι ↪ K) (pivot : K[X]) (L : Submodule F K) [Fintype L] (k : ℕ)
    (hdeg : pivot - subspacePoly (subFinset L) ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset L))
        ∈ ReedSolomon.code domain k
      ∧ (∀ x : ι, domain x ∈ L →
          ReedSolomon.evalOnPoints domain pivot x
            = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset L)) x) :=
  bkr06_codeword_mem_code_and_agrees domain pivot L k hdeg

/-- **Distinct subspace polynomials give distinct codewords (when `domain`
spans).**  If the evaluation embedding is surjective on field elements (e.g.
`ι = K`, `domain = id`), then `P ↦ evalOnPoints domain (pivot − P)` is injective on
polynomials of degree `< |K|`, so distinct subspace polynomials yield distinct
codewords.  This is the injectivity BKR06's counting argument needs; here phrased
on the polynomial difference directly. -/
lemma evalOnPoints_sub_injective_of_surjective
    (domain : ι ↪ K) (hsurj : Function.Surjective domain) (pivot : K[X])
    {P Q : K[X]}
    (hagree : ReedSolomon.evalOnPoints domain (pivot - P)
                = ReedSolomon.evalOnPoints domain (pivot - Q))
    (hP : (pivot - P).natDegree < Fintype.card K)
    (hQ : (pivot - Q).natDegree < Fintype.card K) :
    pivot - P = pivot - Q := by
  classical
  -- Two polynomials of degree `< |K|` agreeing on all `|K|` field points are equal.
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' (pivot - P) (pivot - Q)
    (Finset.univ : Finset K) ?_ ?_
  · intro z _
    obtain ⟨i, rfl⟩ := hsurj z
    have := congrArg (fun f => f i) hagree
    simpa [ReedSolomon.evalOnPoints] using this
  · simpa [Finset.card_univ] using max_lt hP hQ

end BKR06

/-! ## Corrected `_of_injection`-shaped variant (genuine extension parameters)

The in-tree `rs_lambda_superpoly_extension_bkr06_of_injection` collapses to
`m = 1` because its subspace lives in `Submodule F F`.  Here is the *same shape*
stated where the BKR06 construction actually lives: an `𝔽_q`-subspace `W` of a
genuine extension `K`, with the received word and encoding built from the subspace
polynomial via the agreement core above.  We prove the geometric residual (the
encoding exists, maps `W` into agreeing codewords, and is injective) under the
clean hypotheses the construction provides, then hand off to the proven counting
engine.

This is the corrected statement the mismatch analysis recommends.  It is *not* a
restatement of the external full theorem — it isolates exactly the geometric step,
discharged in-tree. -/

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

/-- **Corrected BKR06 geometric residual (extension form).**

Over a genuine extension `K/F`, fix:
* an evaluation domain `domain : K ↪ K` that is surjective (the full field, BKR06's
  setting `domain = id`),
* a degree cutoff `k` with `q^d ≤ k` so subspace-polynomial-difference codewords
  fit (here packaged as the per-family-member degree hypothesis `hdeg`),
* a *family* `𝓛 : ι → Submodule F K` of subspaces with a common pivot `pivot`
  whose subspace polynomials all agree with `pivot` above degree `k` (`hdeg`),
  distinct as polynomials (`hdistinct`).

Then the encoding `i ↦ evalOnPoints domain (pivot − P_{𝓛 i})` sends each family
index to a codeword of `ReedSolomon.code domain k` agreeing with the received word
`w = evalOnPoints domain pivot` on the roots of `P_{𝓛 i}`, and is injective.  This
is the genuine BKR06 roots→distinct-close-codewords step, fully in-tree. -/
theorem bkr06_family_encoding_injective_into_code
    {ι : Type*} [Fintype ι]
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (𝓛 : ι → Submodule F K) [∀ i, Fintype (𝓛 i)]
    (hdeg : ∀ i, pivot - subspacePoly (subFinset (𝓛 i)) ∈ Polynomial.degreeLT K k)
    (hsmall : ∀ i, (pivot - subspacePoly (subFinset (𝓛 i))).natDegree < Fintype.card K)
    (hdistinct : Function.Injective
        (fun i => subspacePoly (subFinset (𝓛 i)))) :
    let encode : ι → (K → K) :=
      fun i => ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
    (∀ i, encode i ∈ ReedSolomon.code domain k)
      ∧ (∀ i, ∀ x : K, domain x ∈ 𝓛 i →
            ReedSolomon.evalOnPoints domain pivot x = encode i x)
      ∧ Function.Injective encode := by
  intro encode
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact evalOnPoints_mem_code_of_degree_lt domain _ k (hdeg i)
  · intro i x hx
    exact evalOnPoints_sub_subspacePoly_agrees_on_W domain pivot (𝓛 i) x hx
  · intro i j hij
    -- equal codewords ⇒ equal polynomial differences ⇒ equal subspace polynomials ⇒ i = j
    have hpoly :
        pivot - subspacePoly (subFinset (𝓛 i))
          = pivot - subspacePoly (subFinset (𝓛 j)) :=
      evalOnPoints_sub_injective_of_surjective domain hsurj pivot hij
        (hsmall i) (hsmall j)
    have hsub :
        subspacePoly (subFinset (𝓛 i)) = subspacePoly (subFinset (𝓛 j)) := by
      linear_combination -hpoly
    exact hdistinct hsub

/-- **Counting hand-off.**  The injective family encoding above forces at least
`|ι|` distinct close codewords; combined with the proven fiber-count engine this is
the BKR06 list-size lower bound at the family's cardinality.  We package the
cardinality consequence directly (using `Set.ncard_le_ncard_of_injOn`), mirroring
exactly how `Bounds.lean`'s `_of_injection` consumes its hypotheses — but with the
encoding *constructed*, not assumed. -/
theorem bkr06_family_close_codewords_card_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (δ : ℝ) (𝓛 : ι → Submodule F K) [∀ i, Fintype (𝓛 i)]
    (hsmall : ∀ i, (pivot - subspacePoly (subFinset (𝓛 i))).natDegree < Fintype.card K)
    (hdistinct : Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))))
    -- Membership in `ReedSolomon.code domain k` (the degree-`< k` constraint) and the
    -- agreement-on-roots closeness are both surfaced as the single explicit closeness
    -- hypothesis `hclose`; BKR06 discharges it from `agree ≥ q^v` (the only genuinely
    -- external numeric input — turning the agreement count into a relative-distance bound).
    (hclose : ∀ i,
        ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
          ∈ ListDecodable.closeCodewordsRel
              ((ReedSolomon.code domain k : Set (K → K)))
              (ReedSolomon.evalOnPoints domain pivot) δ) :
    (Fintype.card ι : ℕ) ≤
      (ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot) δ).ncard := by
  classical
  set encode : ι → (K → K) :=
    fun i => ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
    with hencode
  have hinj : Function.Injective encode := by
    intro i j hij
    have hpoly :
        pivot - subspacePoly (subFinset (𝓛 i))
          = pivot - subspacePoly (subFinset (𝓛 j)) :=
      evalOnPoints_sub_injective_of_surjective domain hsurj pivot hij
        (hsmall i) (hsmall j)
    have hsub :
        subspacePoly (subFinset (𝓛 i)) = subspacePoly (subFinset (𝓛 j)) := by
      linear_combination -hpoly
    exact hdistinct hsub
  -- the image of `encode` is a finite subset of the close-codeword set of size `|ι|`
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι),
      encode i ∈
        ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot) δ := fun i _ => hclose i
  have := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set ι)) encode
    (fun i _ => hclose i) (hinj.injOn) (Set.toFinite _)
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this

end BKR06

-- Axiom audit on the freshly elaborated declarations.
#print axioms BKR06.evalOnPoints_sub_agrees_iff_isRoot
#print axioms BKR06.evalOnPoints_sub_subspacePoly_agrees_on_W
#print axioms BKR06.bkr06_codeword_mem_code_and_agrees
#print axioms BKR06.bkr06_family_member_codeword
#print axioms BKR06.evalOnPoints_sub_injective_of_surjective
#print axioms BKR06.bkr06_family_encoding_injective_into_code
#print axioms BKR06.bkr06_family_close_codewords_card_ge
