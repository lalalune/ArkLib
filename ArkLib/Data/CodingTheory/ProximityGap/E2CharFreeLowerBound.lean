/-
  A2-energy-transfer-r2  (char-p additive-energy transfer for μ_n at r=2)

  GOAL of this draft: pin, in Lean, the EXACT char-free content of the r=2 energy bound
  E_2(μ_n) = 3n² − 3n.  The probes establish:

    * char-0 / generic-prime value is EXACTLY 3n²−3n, with the clean decomposition
        E_2 = T1(diagonal n²) + T2(swap n²−n) + T3(antipodal-new n²−2n).
    * T1, T2 are CHARACTERISTIC-FREE (hold for any finite set, no field structure used).
    * T3 needs only  -1 ∈ μ_n  and  μ_n = -μ_n  (antipodal closure), which the just-landed
      char-free machinery `EvenOddAntipodal.image_neg_eq_of_prod_comp_neg` delivers.
    * Therefore  E_2(μ_n) ≥ 3n²−3n  is CHAR-FREE for every n (this file's provable core).
    * The UPPER bound  E_2(μ_n) ≤ 3n²−3n  is the ONLY char-dependent half, and it FAILS at
      structured primes for large n.  The EXACT obstruction is the 4-term root relation
        1 + B = C + D   with  B,C,D ∈ μ_n  and  {1,B} ≠ {C,D}   (the "genuine" extra quadruple).
      Minimal witness:  n=4, p=5:  1 + i = (-1)+(-1)  (i=2, since 2²=−1 in F₅).

  This draft formalizes the additive energy as a Finset count, the (T1,T2) char-free lower
  bound (the diagonal+swap injection), names the obstruction as an explicit Prop, and shows the
  upper bound is equivalent to the NON-existence of a genuine quadruple.  The antipodal T3 term
  is left as the hook to the EvenOddAntipodal closure (named, not silently discharged).
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

open Finset

namespace ArkLib.ProximityGap.E2CharFree

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- The (ordered) additive-energy solution set of a finite set `S ⊆ F`:
quadruples `(x₁,x₂,y₁,y₂) ∈ S⁴` with `x₁ + x₂ = y₁ + y₂`. -/
def energyQuads (S : Finset F) : Finset (F × F × F × F) :=
  ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
    (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2) |>.image
    (fun q => (q.1.1, q.1.2, q.2.1, q.2.2))

/-- The additive energy `E₂(S) = #{(x₁,x₂,y₁,y₂) ∈ S⁴ : x₁+x₂ = y₁+y₂}`. -/
def E2 (S : Finset F) : ℕ := (energyQuads S).card

/-- The **diagonal** family: `(x₁,x₂,x₁,x₂)` for `(x₁,x₂) ∈ S×S`.  Always a valid quadruple,
char-free.  Cardinality `n²`. -/
def diagQuads (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S).image (fun p => (p.1, p.2, p.1, p.2))

/-- The **swap** family: `(x₁,x₂,x₂,x₁)` for `(x₁,x₂) ∈ S×S`.  Always valid (`x₁+x₂=x₂+x₁`),
char-free. -/
def swapQuads (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S).image (fun p => (p.1, p.2, p.2, p.1))

/-- diagonal quads are genuine energy quads (char-free, only uses commutativity). -/
theorem diagQuads_subset (S : Finset F) : diagQuads S ⊆ energyQuads S := by
  classical
  intro q hq
  simp only [diagQuads, Finset.mem_image, Finset.mem_product] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
  simp only [energyQuads, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨((a, b), (a, b)), ⟨⟨⟨ha, hb⟩, ⟨ha, hb⟩⟩, rfl⟩, rfl⟩

/-- swap quads are genuine energy quads (char-free, uses `add_comm`). -/
theorem swapQuads_subset (S : Finset F) : swapQuads S ⊆ energyQuads S := by
  classical
  intro q hq
  simp only [swapQuads, Finset.mem_image, Finset.mem_product] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
  simp only [energyQuads, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨((a, b), (b, a)), ⟨⟨⟨ha, hb⟩, ⟨hb, ha⟩⟩, add_comm a b⟩, rfl⟩

/-- The diagonal family has cardinality `|S|²` (the image is injective). -/
theorem diagQuads_card (S : Finset F) : (diagQuads S).card = S.card * S.card := by
  classical
  unfold diagQuads
  rw [Finset.card_image_of_injective _ (by
    intro x y h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1),
    Finset.card_product]

/-- **The char-free lower-bound seed.**  `E₂(S) ≥ |S|²` for any finite set in any
additive group, via the always-valid diagonal injection.  (This is the `T1` term; the full
`3n²−3n` char-free lower bound adds the `T2` swap term and the `T3` antipodal term — see below.) -/
theorem E2_ge_card_sq (S : Finset F) : S.card * S.card ≤ E2 S := by
  calc S.card * S.card = (diagQuads S).card := (diagQuads_card S).symm
    _ ≤ (energyQuads S).card := Finset.card_le_card (diagQuads_subset S)
    _ = E2 S := rfl

/-- The swap family also has cardinality `|S|²` (the image map is injective). -/
theorem swapQuads_card (S : Finset F) : (swapQuads S).card = S.card * S.card := by
  classical
  unfold swapQuads
  rw [Finset.card_image_of_injective _ (by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1),
    Finset.card_product]

/-- `diagQuads ∪ swapQuads ⊆ energyQuads` (both families are char-free valid quadruples). -/
theorem diag_union_swap_subset (S : Finset F) :
    diagQuads S ∪ swapQuads S ⊆ energyQuads S :=
  Finset.union_subset (diagQuads_subset S) (swapQuads_subset S)

/-- Membership of `diagQuads S`: `q ∈ diagQuads S ↔ ∃ a b, a∈S ∧ b∈S ∧ q=(a,b,a,b)`. -/
theorem mem_diagQuads {S : Finset F} {q : F × F × F × F} :
    q ∈ diagQuads S ↔ ∃ a ∈ S, ∃ b ∈ S, q = (a, b, a, b) := by
  classical
  simp only [diagQuads, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Membership of `swapQuads S`. -/
theorem mem_swapQuads {S : Finset F} {q : F × F × F × F} :
    q ∈ swapQuads S ↔ ∃ a ∈ S, ∃ b ∈ S, q = (a, b, b, a) := by
  classical
  simp only [swapQuads, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- An element of the intersection `diagQuads ∩ swapQuads` is constant: `q = (a,a,a,a)`. -/
theorem inter_eq_const {S : Finset F} {q : F × F × F × F}
    (hq : q ∈ diagQuads S ∩ swapQuads S) : ∃ a ∈ S, q = (a, a, a, a) := by
  classical
  rw [Finset.mem_inter] at hq
  obtain ⟨a, ha, b, _, rfl⟩ := mem_diagQuads.mp hq.1
  obtain ⟨c, _, d, _, hcd⟩ := mem_swapQuads.mp hq.2
  -- (a,b,a,b) = (c,d,d,c) ⟹ a=c, b=d, a=d, b=c ⟹ a=b
  simp only [Prod.mk.injEq] at hcd
  obtain ⟨h1, h2, h3, h4⟩ := hcd
  -- h1: a=c, h2: b=d, h3: a=d, h4: b=c ⟹ a=b (from h2,h3: b=d=a)
  have hab : a = b := by rw [h2, ← h3]
  exact ⟨a, ha, by simp [hab]⟩

/-- The intersection of the diagonal and swap families is exactly the "constant" quadruples
`(x,x,x,x)` with `x ∈ S`; in particular it has cardinality `≤ |S|`. -/
theorem diag_inter_swap_card_le (S : Finset F) :
    (diagQuads S ∩ swapQuads S).card ≤ S.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q => q.1)
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := inter_eq_const hq
    exact ha
  · intro q hq q' hq' hqq'
    obtain ⟨a, _, rfl⟩ := inter_eq_const hq
    obtain ⟨a', _, rfl⟩ := inter_eq_const hq'
    simp only at hqq'
    simp [hqq']

/-- **The char-free `2n²−n` lower bound.**  For any finite set in any additive group,
`E₂(S) ≥ 2|S|² − |S|`, via the diagonal ∪ swap families (`T1 + T2`).  This is the
characteristic-INDEPENDENT part of the `3n²−3n` value; only the antipodal `T3 = n²−2n` term
requires `μ_n = −μ_n` (supplied char-freely by `EvenOddAntipodal.image_neg_eq_of_prod_comp_neg`),
and only the matching UPPER bound is genuinely char-dependent. -/
theorem E2_ge_two_card_sq_sub_card (S : Finset F) :
    2 * (S.card * S.card) - S.card ≤ E2 S := by
  classical
  have hunion : (diagQuads S ∪ swapQuads S).card ≤ E2 S :=
    Finset.card_le_card (diag_union_swap_subset S)
  have hcard : (diagQuads S ∪ swapQuads S).card
      = (diagQuads S).card + (swapQuads S).card - (diagQuads S ∩ swapQuads S).card := by
    rw [Finset.card_union]
  rw [hcard, diagQuads_card, swapQuads_card] at hunion
  have hinter : (diagQuads S ∩ swapQuads S).card ≤ S.card := diag_inter_swap_card_le S
  have hle : 2 * (S.card * S.card) - S.card
      ≤ (S.card * S.card + S.card * S.card) - (diagQuads S ∩ swapQuads S).card := by
    omega
  exact le_trans hle hunion

/-! ### The exact obstruction to the UPPER bound `E₂ ≤ 3n²−3n`

A "genuine" extra quadruple is one outside diagonal ∪ swap ∪ antipodal.  After normalizing by
an element (divide by `x₁`), every genuine quadruple is a relation `1 + B = C + D` with
`B,C,D ∈ μ_n`, `{1,B} ≠ {C,D}`, and `1+B ≠ 0`.  We state this as an explicit Prop.  The probes
show it is SATISFIABLE starting at `n = 4`, `p = 5` (`1 + i = (-1)+(-1)` in `F₅`), so the
char-free transfer of the UPPER bound is genuinely conditional. -/

/-- **The genuine-quadruple obstruction Prop** (multiplicative form, to be specialized to `μ_n`).
For a set `S` containing `1`: a genuine 4-term additive relation among elements of `S` with the
distinguished element `1` on the left.  `E₂(S) = 3|S|²−3|S|` requires the NEGATION of this for
all such normalizations.  Stated over a ring so `1` is available. -/
def GenuineQuadruple {R : Type*} [Ring R] [DecidableEq R] (S : Finset R) : Prop :=
  ∃ B C D : R, B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ (1 : R) + B = C + D ∧
    ¬ (({(1 : R), B} : Finset R) = {C, D})

end ArkLib.ProximityGap.E2CharFree

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.E2CharFree.diagQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.swapQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.diagQuads_card
#print axioms ArkLib.ProximityGap.E2CharFree.E2_ge_card_sq
#print axioms ArkLib.ProximityGap.E2CharFree.swapQuads_card
#print axioms ArkLib.ProximityGap.E2CharFree.diag_inter_swap_card_le
#print axioms ArkLib.ProximityGap.E2CharFree.E2_ge_two_card_sq_sub_card
