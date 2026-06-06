/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# GGR11 interleaved-code list-size recursion — residual reduction

This file isolates the **single external obstruction** behind ABF26 Lemma 2.10
(= Gopalan–Guruswami–Raghavendra 2011, "List Decoding Tensor Products and
Interleaved Codes", RANDOM 2011) so that `lambda_le_ggr11` in
`ArkLib.Data.CodingTheory.InterleavedCode` can be discharged *modulo a single,
precisely named combinatorial hypothesis* with **no `sorry` and no `axiom`** in
the reduction itself.

## The theorem

Let `C ⊆ (ι → F)` be a code with relative minimum distance `δ_C := δ_min(C)/|ι|`,
and `δ ∈ [0, δ_C)`. With `η := δ_C - δ`, `b := ⌈δ/η⌉`, `r := ⌈log₂(δ_C/η)⌉`,
GGR11 / ABF26 L2.10 states, for every `m ≥ 1`,

  `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r`.   (★)

## What is in-tree, what is the residual

`ArkLib.Data.CodingTheory.InterleavedListSize` proves, fully `sorry`-free, the
elementary `m`-*dependent* bound

  `|Λ(C^{≡m}, δ)| ≤ |Λ(C, δ)|^m`   (the per-column product bound),

via the injection `V ↦ (V.transpose ·)` of a close interleaved codeword into the
product of its per-column base-code lists.  That is the deepest in-tree-reachable
statement: it uses only the row/column projection lemmas.

The improvement of (★) over the product bound is the replacement of the exponent
`m` by the `m`-*independent* `r = ⌈log₂(δ_C/η)⌉`, together with the `(b+r choose
r)` prefactor.  Achieving `m`-independence is exactly the GGR11 list-recovery /
column-pruning recursion: of the `m` columns, only `r` "pivot" columns carry
independent list freedom (a budget/covering argument over the `b`-bounded
agreement deficits), and the joint list embeds into the product of the per-pivot
lists.  ArkLib presently has **no list-recovery primitive and no column-pruning /
iterated-projection lemma**, so this step is a genuine external-paper wall, not a
missing local proof.

We therefore name precisely that wall — the per-received-word form of (★) — as
`GGR11PerWordBound`, and prove that it implies (★) for the maximised `Lambda`.
This converts the live `sorry` into a single, auditable named hypothesis.

## Edge cases discharged unconditionally

`lambda_le_ggr11` itself (in `InterleavedCode.lean`) already closes the
infinite-list case `Λ(C, δ) = ⊤` completely (the RHS is then `⊤`).  Here we also
record `lambda_le_ggr11_of_perWordBound`, the finite-regime reduction.

## The closed-form combinatorics is now in-tree (NEW)

GGR11 §3 splits into two parts:

* **(Tree construction.)** Build `Tree(R)`, the Erase-Decode tree (Algorithm 1).
  Its number of leaves bounds the per-word list size.  After contracting White
  edges (Lemma 3.3: a White edge is the *only* edge out of its node), every node
  has at most **one** Blue out-edge (Lemma 3.4) and at most `|Λ(C,δ)|` Red
  out-edges; every root→leaf path has at most `b` Blue edges (Lemma 3.4) and at
  most `r` Red edges (Lemma 3.5).  This is the list-recovery / erasure-decoding
  content that has **no in-tree analogue**.

* **(Leaf counting.)** A tree with those per-node and per-path budgets has at
  most `(b+r choose r)·|Λ(C,δ)|^r` leaves (Theorem 3.6), via the recursion
  `t(b,r) ≤ t(b-1,r) + L·t(b,r-1)`, base `t(b,0) = 1`.

We now prove the **second** part fully (`ggr11_tree_count_le`, no `sorry`/`axiom`),
and refactor the residual so that it names *only the first part* — the existence
of a leaf-count function satisfying the GGR11 budget recursion that dominates the
actual close set (`GGR11TreeStructure`).  The chain

  `GGR11TreeFrontier ↔ GGR11TreeStructure → GGR11PerWordBound → lambda_le_ggr11`

is then fully proven (`perWordBound_of_treeStructure`,
`perWordBound_of_treeFrontier`, `lambda_le_ggr11_of_perWordBound`).  This shrinks
the named external surface from "the whole §3 recursion incl. the closed-form
`choose` bound" down to "the Erase-Decode tree exists with the stated Blue/Red
budgets", with the per-word witness data named explicitly.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.GGR11

variable {ι F : Type} [Fintype ι]

/-- **The GGR11 residual (per-received-word form).**

For a fixed received interleaved word `f : Matrix ι (Fin m) F`, the number of
interleaved codewords `δ`-close to `f` is at most `(b+r choose r) · |Λ(C,δ)|^r`,
with `r` (and `b`) the GGR11 exponent/prefactor — **independent of `m`**.

This is exactly the content GGR11 §3 establishes by the list-recovery /
column-pruning recursion described in the module docstring.  It is stated as an
`encard` bound so that it is meaningful over an arbitrary (possibly infinite)
field `F`, with no `Fintype F` assumption: when a per-column list is infinite the
hypothesis is vacuously informative on the `⊤` side, and the genuine content is
the finite case.

We do **not** prove this here: it is the named external obstruction. -/
def GGR11PerWordBound (C : Set (ι → F)) (δ : ℝ) (m b r : ℕ) : Prop :=
  ∀ f : Matrix ι (Fin m) F,
    (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r

/-- **Reduction of the GGR11 interleaved list-size bound to its per-word form.**

Given the per-received-word bound `GGR11PerWordBound`, the maximised list size
`Lambda (C^{≡m}) δ` obeys the same bound.  The lift is a routine `iSup`/`ncard ≤
encard` argument; *all* the mathematical depth lives in the hypothesis. -/
theorem lambda_le_ggr11_of_perWordBound
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11PerWordBound C δ m b r) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  refine iSup_le (fun f => ?_)
  calc ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).ncard : ℕ∞)
      ≤ (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard :=
        Set.ncard_le_encard _
    _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := h f

/-! ### The GGR11 leaf-counting recursion (Theorem 3.6) — fully in-tree -/

/-- **GGR11 Theorem 3.6, leaf-counting bound (no external input).**

Let `L : ℕ∞` be a per-node Red branching bound (in the application,
`L = Λ(C,δ)`).  Suppose `t b r : ℕ∞` is *any* upper bound on the number of leaves
of a rooted tree in which

* every root→leaf path has at most `b` Blue and `r` Red edges,
* every node has at most one Blue out-edge and at most `L` Red out-edges,

encoded by the three structural inequalities below (`hbase`: a tree with no Red
budget has a single leaf; `hrec0`: the Red-only column branches by `≤ L`;
`hrec`: Pascal's recursion `t(b,r) ≤ t(b-1,r) + L·t(b,r-1)`).  Then

  `t b r ≤ (b+r choose r) · L^r`.

This is the entire combinatorial content of GGR11 Theorem 3.6, proved here with
**no `sorry` and no `axiom`** by the double induction the paper indicates
("It is easy to check that `t(b, r) ≤ (b+r choose r)·ℓ^r`"). -/
theorem ggr11_tree_count_le
    (L : ℕ∞) (t : ℕ → ℕ → ℕ∞)
    (hbase : ∀ b, t b 0 ≤ 1)
    (hrec0 : ∀ r, t 0 (r + 1) ≤ L * t 0 r)
    (hrec : ∀ b r, t (b + 1) (r + 1) ≤ t b (r + 1) + L * t (b + 1) r) :
    ∀ b r, t b r ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
  intro b r
  induction r generalizing b with
  | zero => simpa using hbase b
  | succ r ih =>
    induction b with
    | zero =>
      calc t 0 (r + 1)
          ≤ L * t 0 r := hrec0 r
        _ ≤ L * (((0 + r).choose r : ℕ∞) * L ^ r) := by
              exact mul_le_mul' (le_refl L) (ih 0)
        _ = ((0 + r).choose r : ℕ∞) * L ^ (r + 1) := by ring
        _ = ((0 + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
              simp [Nat.choose_self]
    | succ b ihb =>
      calc t (b + 1) (r + 1)
          ≤ t b (r + 1) + L * t (b + 1) r := hrec b r
        _ ≤ ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1)
              + L * (((b + 1) + r).choose r * L ^ r) := by
              refine add_le_add ihb ?_
              exact mul_le_mul' (le_refl L) (ih (b + 1))
        _ = (((b + (r + 1)).choose (r + 1) : ℕ∞)
              + ((b + 1 + r).choose r : ℕ∞)) * L ^ (r + 1) := by ring
        _ = (((b + 1) + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
              congr 1
              have hsplit : (b + 1) + (r + 1) = (b + (r + 1)) + 1 := by ring
              rw [hsplit, Nat.choose_succ_succ (b + (r + 1)) r]
              push_cast
              have e1 : b + (r + 1) = b + r + 1 := by ring
              have e2 : b + 1 + r = b + r + 1 := by ring
              rw [e1, e2]
              ring

/-! ### The refined residual: only the Erase-Decode tree existence -/

/-- **The GGR11 residual, refined to tree existence only.**

For a fixed received interleaved word `f`, there exists a leaf-count function
`t : ℕ → ℕ → ℕ∞` such that the close-codeword set is dominated by `t b r`, and `t`
obeys the GGR11 Erase-Decode budget recursion with Red branching factor
`L = Λ(C,δ)` (cf. `ggr11_tree_count_le`).

This is **strictly smaller** than `GGR11PerWordBound`: it names only the existence
of the Erase-Decode tree with the Blue/Red budgets of GGR11 Lemmas 3.3–3.5 (the
list-recovery / erasure-decoding content with no in-tree analogue), and **drops**
the closed-form `(b+r choose r)·L^r` combinatorics, which is now the proved lemma
`ggr11_tree_count_le`. -/
def GGR11TreeStructure (C : Set (ι → F)) (δ : ℝ) (m b r : ℕ) : Prop :=
  ∀ f : Matrix ι (Fin m) F,
    ∃ t : ℕ → ℕ → ℕ∞,
      (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard ≤ t b r ∧
      (∀ b', t b' 0 ≤ 1) ∧
      (∀ r', t 0 (r' + 1) ≤ (Lambda C δ) * t 0 r') ∧
      (∀ b' r', t (b' + 1) (r' + 1) ≤ t b' (r' + 1) + (Lambda C δ) * t (b' + 1) r')

/-- Named per-received-word witness for the GGR11 Erase-Decode tree residual.

This is the non-anonymous form of one `f`-instance of `GGR11TreeStructure`: a leaf-count
function plus the Blue/Red budget inequalities that feed `ggr11_tree_count_le`.  Naming it
separates the future tree-construction work from the already-proved closed-form counting lemma. -/
structure GGR11TreeWitness (C : Set (ι → F)) (δ : ℝ) (m b r : ℕ)
    (f : Matrix ι (Fin m) F) where
  leafCount : ℕ → ℕ → ℕ∞
  close_le_leafCount :
    (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard ≤ leafCount b r
  no_red_budget : ∀ b', leafCount b' 0 ≤ 1
  red_only_step : ∀ r', leafCount 0 (r' + 1) ≤ (Lambda C δ) * leafCount 0 r'
  blue_red_step :
    ∀ b' r',
      leafCount (b' + 1) (r' + 1) ≤
        leafCount b' (r' + 1) + (Lambda C δ) * leafCount (b' + 1) r'

/-- Granular frontier for the remaining GGR11 construction: every received word has a named
Erase-Decode tree witness satisfying the Blue/Red budget recursion. -/
def GGR11TreeFrontier (C : Set (ι → F)) (δ : ℝ) (m b r : ℕ) : Prop :=
  ∀ f : Matrix ι (Fin m) F, Nonempty (GGR11TreeWitness C δ m b r f)

/-- The named frontier is exactly strong enough to recover the existing residual shape. -/
theorem treeStructure_of_frontier
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeFrontier C δ m b r) :
    GGR11TreeStructure C δ m b r := by
  intro f
  obtain ⟨w⟩ := h f
  exact
    ⟨w.leafCount, w.close_le_leafCount, w.no_red_budget, w.red_only_step,
      w.blue_red_step⟩

/-- Conversely, the existing residual immediately supplies the named frontier. -/
theorem frontier_of_treeStructure
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeStructure C δ m b r) :
    GGR11TreeFrontier C δ m b r := by
  intro f
  obtain ⟨t, hdom, hbase, hrec0, hrec⟩ := h f
  exact
    ⟨
      { leafCount := t
        close_le_leafCount := hdom
        no_red_budget := hbase
        red_only_step := hrec0
        blue_red_step := hrec }
    ⟩

/-- **The closed-form combinatorics discharges `GGR11PerWordBound` from
`GGR11TreeStructure`.**

Given the Erase-Decode tree (the refined residual), the per-word bound follows by
the fully-proven leaf-counting lemma `ggr11_tree_count_le`.  No `sorry`/`axiom`. -/
theorem perWordBound_of_treeStructure
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeStructure C δ m b r) :
    GGR11PerWordBound C δ m b r := by
  intro f
  obtain ⟨t, hdom, hbase, hrec0, hrec⟩ := h f
  calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ t b r := hdom
    _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
        ggr11_tree_count_le (Lambda C δ) t hbase hrec0 hrec b r

/-- The named frontier also reassembles to the per-word GGR11 bound. -/
theorem perWordBound_of_treeFrontier
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeFrontier C δ m b r) :
    GGR11PerWordBound C δ m b r :=
  perWordBound_of_treeStructure (treeStructure_of_frontier h)

/-- **End-to-end:** the GGR11 interleaved list-size bound from the refined
tree-existence residual. -/
theorem lambda_le_ggr11_of_treeStructure
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeStructure C δ m b r) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_perWordBound (perWordBound_of_treeStructure h)

/-- End-to-end GGR11 list-size bound from the granular named frontier. -/
theorem lambda_le_ggr11_of_treeFrontier
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11TreeFrontier C δ m b r) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_treeStructure (treeStructure_of_frontier h)

set_option linter.unusedFintypeInType false in
/-- **The refined residual is inhabited in the elementary regime.**

When `m ≤ r` and `1 ≤ Λ(C,δ)`, the in-tree product bound
`encard ≤ Λ(C,δ)^m` already supplies a GGR11 Erase-Decode tree: take the explicit
leaf-count `t b' r' := Λ(C,δ)^{r'}` (a tree of pure Red depth, which trivially
meets all the Blue/Red budgets), which dominates the close set because
`Λ(C,δ)^m ≤ Λ(C,δ)^r = t b r`.  This shows `GGR11TreeStructure` is **not
vacuous** and is consistent with the in-tree elementary product bound; it is the
complementary `m > r` regime (where `t b' r' := Λ^{r'}` no longer dominates) that
needs the genuine GGR11 erasure-decoding construction. -/
theorem ggr11_treeStructure_of_le_exp [Fintype F] [Nonempty ι]
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hmr : m ≤ r) (hL : 1 ≤ Lambda C δ) :
    GGR11TreeStructure C δ m b r := by
  intro f
  refine ⟨fun _ r' => (Lambda C δ) ^ r', ?_, ?_, ?_, ?_⟩
  · -- domination: encard ≤ Λ^m ≤ Λ^r = t b r
    calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
        ≤ (Lambda C δ) ^ m :=
          InterleavedCode.ListSize.encard_closeCodewordsRel_interleaved_le f
      _ ≤ (Lambda C δ) ^ r := pow_le_pow_right₀ hL hmr
  · -- base: Λ^0 = 1 ≤ 1
    intro b'; simp
  · -- Red column: Λ^(r'+1) ≤ Λ · Λ^(r')  (equality)
    intro r'; simp only; rw [pow_succ, mul_comm]
  · -- Pascal: Λ^(r'+1) ≤ Λ^(r'+1) + Λ · Λ^(r')
    intro b' r'; simp only; exact le_add_right (le_refl _)
/-- If the base list size is infinite and the GGR11 exponent is positive, the per-word residual is
automatic: the RHS is `⊤`. This discharges the infinite-list edge case and leaves only the finite
list-recovery recursion as genuine external content. -/
theorem ggr11_perWordBound_of_Lambda_top
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hr : 0 < r) (hL : Lambda C δ = ⊤) :
    GGR11PerWordBound C δ m b r := by
  intro f
  rw [hL]
  cases r with
  | zero => cases hr
  | succ r =>
      have hchoose_pos : 0 < (b + (r + 1)).choose (r + 1) :=
        Nat.choose_pos (Nat.le_add_left (r + 1) b)
      have hchoose_ne :
          (((b + (r + 1)).choose (r + 1) : ℕ) : ℕ∞) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hchoose_pos)
      rw [show (⊤ : ℕ∞) ^ (r + 1) = ⊤ by simp]
      rw [ENat.mul_top hchoose_ne]
      exact le_top

set_option linter.unusedFintypeInType false in
/-- Over a *finite* field the in-tree elementary product bound discharges the
GGR11 residual whenever the GGR11 exponent `r` already dominates the interleaving
factor `m` **and** the base list size is at least one — i.e. exactly the regime
in which `m`-independence carries no extra information.  Concretely, if `m ≤ r`
and `1 ≤ Λ(C,δ)`, then
`|Λ(C^{≡m},δ)| ≤ |Λ(C,δ)|^m ≤ |Λ(C,δ)|^r ≤ (b+r choose r)·|Λ(C,δ)|^r`.

This is **not** the GGR11 content (which is the complementary `m > r` regime); it
is a sanity sub-case showing the reduction is consistent with the in-tree bound.
It now factors through the refined residual via `ggr11_treeStructure_of_le_exp`. -/
theorem ggr11_perWordBound_of_le_exp [Fintype F] [Nonempty ι]
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hmr : m ≤ r) (hL : 1 ≤ Lambda C δ) :
    GGR11PerWordBound C δ m b r := by
  intro f
  have hpow : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ (Lambda C δ) ^ m :=
    InterleavedCode.ListSize.encard_closeCodewordsRel_interleaved_le f
  have hexp : (Lambda C δ) ^ m ≤ (Lambda C δ) ^ r := pow_le_pow_right₀ hL hmr
  have hbinom : (1 : ℕ∞) ≤ ((b + r).choose r : ℕ∞) := by
    have : 1 ≤ (b + r).choose r := Nat.choose_pos (Nat.le_add_left r b)
    exact_mod_cast this
  calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ (Lambda C δ) ^ m := hpow
    _ ≤ (Lambda C δ) ^ r := hexp
    _ = 1 * (Lambda C δ) ^ r := (one_mul _).symm
    _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
          gcongr

/-- Generic end-to-end elementary regime: if the Red budget already dominates the
interleaving factor, the in-tree product bound proves the GGR11 list-size conclusion. -/
theorem lambda_le_ggr11_of_le_exp [Fintype F] [Nonempty ι]
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hmr : m ≤ r) (hL : 1 ≤ Lambda C δ) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_perWordBound (ggr11_perWordBound_of_le_exp hmr hL)

/-- Generic end-to-end infinite-list regime: if the base list size is infinite and the
Red budget is positive, the right-hand side is `⊤`, so the GGR11 list-size conclusion is
automatic. -/
theorem lambda_le_ggr11_of_Lambda_top
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hr : 0 < r) (hL : Lambda C δ = ⊤) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_perWordBound (ggr11_perWordBound_of_Lambda_top hr hL)

-- Axiom audit: generic frontier/reassembly surfaces for the GGR11 tree residual.
#print axioms treeStructure_of_frontier
#print axioms frontier_of_treeStructure
#print axioms perWordBound_of_treeStructure
#print axioms perWordBound_of_treeFrontier
#print axioms lambda_le_ggr11_of_treeStructure
#print axioms lambda_le_ggr11_of_treeFrontier
#print axioms ggr11_treeStructure_of_le_exp
#print axioms ggr11_perWordBound_of_Lambda_top
#print axioms ggr11_perWordBound_of_le_exp
#print axioms lambda_le_ggr11_of_le_exp
#print axioms lambda_le_ggr11_of_Lambda_top

end InterleavedCode.GGR11
