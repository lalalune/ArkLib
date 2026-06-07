/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GGR11Interleaved

/-!
# The GGR11 Erase-Decode tree datatype — a concrete inductive witness

`ArkLib.ToMathlib.GGR11Interleaved` reduced the ABF26 Lemma 2.10 (GGR11 §3)
interleaved list-size bound down to a single named external residual,
`GGR11TreeStructure`: *there exists a leaf-count function `t : ℕ → ℕ → ℕ∞`
dominating the close-codeword set and obeying the GGR11 Blue/Red budget
recursion.*  The abstract residual only ever names `t` as a numeric function; it
never exhibits an actual tree.

This file supplies the missing **concrete inductive datatype** behind that
abstraction: the Erase-Decode tree of GGR11 Algorithm 1, *after* the structural
simplifications of Lemmas 3.3–3.5 (White edges contracted, so every internal node
has at most one Blue out-edge and a finite list of Red out-edges).

## What is proved here (fully, no `sorry`/`axiom`)

* `EraseDecodeTree` — an inductive tree with one optional Blue child and a `List`
  of Red children (the contracted Algorithm-1 shape).
* `leafCount`, `blueDepth`, `redDepth`, `redBranchingLe L` — the leaf count and
  the max Blue / Red edges on any root→leaf path, plus the predicate "every node
  has at most `L` Red children".
* `EraseDecodeTree.leafCount_le` — **GGR11 Theorem 3.6 for a genuine tree**: for
  any tree with `blueDepth ≤ b`, `redDepth ≤ r`, and `redBranchingLe L`,

    `leafCount ≤ (b + r choose r) · L ^ r`,

  proved by well-founded recursion matching the Pascal recursion
  `t(b,r) ≤ t(b-1,r) + L·t(b,r-1)` that `ggr11_tree_count_le` formalises.

## How this connects to the residual

This makes the abstract `GGR11TreeStructure` residual *constructively witnessed*:
any actual Erase-Decode tree dominating the close set immediately yields the
abstract leaf-count function (`treeStructure_of_eraseDecodeTree`).  What remains
external is only the *construction* of such a tree from the erasure-decoding
algorithm in the hard `m > r` regime — the list-recovery content with no in-tree
analogue.  The datatype, its leaf-count budget theorem, and the bridge to the
named residual are all in-tree here.
-/

namespace InterleavedCode.GGR11

/-- **The (contracted) GGR11 Erase-Decode tree.**

A node is either a `leaf`, or an internal `node` carrying:
* `blue : Option EraseDecodeTree` — at most one Blue out-edge (Lemma 3.4), and
* `red  : List EraseDecodeTree`   — the finitely many Red out-edges.

This is the shape of GGR11 Algorithm 1's tree after Lemma 3.3 contracts every
White edge (a White edge is the unique edge out of its node, so it never
branches). -/
inductive EraseDecodeTree where
  | leaf : EraseDecodeTree
  | node : Option EraseDecodeTree → List EraseDecodeTree → EraseDecodeTree

namespace EraseDecodeTree

mutual
  /-- Number of leaves of an Erase-Decode tree (as `ℕ∞`, so it composes with the
  `Lambda`-valued budgets).  A leaf contributes `1`; an internal node sums its Blue
  subtree (if present) and all its Red subtrees. -/
  def leafCount : EraseDecodeTree → ℕ∞
    | leaf => 1
    | node b rs => leafCountOption b + leafCountList rs

  def leafCountOption : Option EraseDecodeTree → ℕ∞
    | none => 0
    | some t => leafCount t

  def leafCountList : List EraseDecodeTree → ℕ∞
    | [] => 0
    | t :: ts => leafCount t + leafCountList ts
end

mutual
  /-- Maximum number of Blue edges on any root→leaf path. -/
  def blueDepth : EraseDecodeTree → ℕ
    | leaf => 0
    | node b rs => max (blueDepthOption b) (blueDepthList rs)

  def blueDepthOption : Option EraseDecodeTree → ℕ
    | none => 0
    | some t => blueDepth t + 1

  def blueDepthList : List EraseDecodeTree → ℕ
    | [] => 0
    | t :: ts => max (blueDepth t) (blueDepthList ts)
end

mutual
  /-- Maximum number of Red edges on any root→leaf path. -/
  def redDepth : EraseDecodeTree → ℕ
    | leaf => 0
    | node b rs => max (redDepthOption b) (redDepthList rs)

  def redDepthOption : Option EraseDecodeTree → ℕ
    | none => 0
    | some t => redDepth t

  def redDepthList : List EraseDecodeTree → ℕ
    | [] => 0
    | t :: ts => max (redDepth t + 1) (redDepthList ts)
end

mutual
  /-- `redBranchingLe L t`: every node of `t` has at most `L` Red children. -/
  def redBranchingLe (L : ℕ∞) : EraseDecodeTree → Prop
    | leaf => True
    | node b rs =>
        redBranchingLeOption L b ∧
        (rs.length : ℕ∞) ≤ L ∧
        redBranchingLeList L rs

  def redBranchingLeOption (L : ℕ∞) : Option EraseDecodeTree → Prop
    | none => True
    | some t => redBranchingLe L t

  def redBranchingLeList (L : ℕ∞) : List EraseDecodeTree → Prop
    | [] => True
    | t :: ts => redBranchingLe L t ∧ redBranchingLeList L ts
end

@[simp] theorem leafCount_leaf : leafCount leaf = 1 := by rw [leafCount]

@[simp] theorem blueDepth_leaf : blueDepth leaf = 0 := by rw [blueDepth]

@[simp] theorem redDepth_leaf : redDepth leaf = 0 := by rw [redDepth]

@[simp] theorem redBranchingLe_leaf (L : ℕ∞) : redBranchingLe L leaf := trivial

@[simp] theorem leafCountOption_none : leafCountOption none = 0 := by rw [leafCountOption]

@[simp] theorem leafCountOption_some (t : EraseDecodeTree) :
    leafCountOption (some t) = leafCount t := by
  rw [leafCountOption]

@[simp] theorem leafCountList_nil : leafCountList [] = 0 := by rw [leafCountList]

@[simp] theorem leafCountList_cons (t : EraseDecodeTree) (ts : List EraseDecodeTree) :
    leafCountList (t :: ts) = leafCount t + leafCountList ts := by
  rw [leafCountList]

@[simp] theorem blueDepthOption_none : blueDepthOption none = 0 := by rw [blueDepthOption]

@[simp] theorem blueDepthOption_some (t : EraseDecodeTree) :
    blueDepthOption (some t) = blueDepth t + 1 := by
  rw [blueDepthOption]

@[simp] theorem blueDepthList_nil : blueDepthList [] = 0 := by rw [blueDepthList]

@[simp] theorem blueDepthList_cons (t : EraseDecodeTree) (ts : List EraseDecodeTree) :
    blueDepthList (t :: ts) = max (blueDepth t) (blueDepthList ts) := by
  rw [blueDepthList]

@[simp] theorem redDepthOption_none : redDepthOption none = 0 := by rw [redDepthOption]

@[simp] theorem redDepthOption_some (t : EraseDecodeTree) :
    redDepthOption (some t) = redDepth t := by
  rw [redDepthOption]

@[simp] theorem redDepthList_nil : redDepthList [] = 0 := by rw [redDepthList]

@[simp] theorem redDepthList_cons (t : EraseDecodeTree) (ts : List EraseDecodeTree) :
    redDepthList (t :: ts) = max (redDepth t + 1) (redDepthList ts) := by
  rw [redDepthList]

@[simp] theorem redBranchingLeOption_none (L : ℕ∞) : redBranchingLeOption L none :=
  trivial

@[simp] theorem redBranchingLeOption_some (L : ℕ∞) (t : EraseDecodeTree) :
    redBranchingLeOption L (some t) ↔ redBranchingLe L t := by
  rw [redBranchingLeOption]

@[simp] theorem redBranchingLeList_nil (L : ℕ∞) : redBranchingLeList L [] :=
  trivial

@[simp] theorem redBranchingLeList_cons (L : ℕ∞) (t : EraseDecodeTree)
    (ts : List EraseDecodeTree) :
    redBranchingLeList L (t :: ts) ↔ redBranchingLe L t ∧ redBranchingLeList L ts := by
  rw [redBranchingLeList]

theorem leafCount_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    leafCount (node b rs)
      = leafCountOption b + leafCountList rs := by
  rw [leafCount]

theorem blueDepth_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    blueDepth (node b rs)
      = max (blueDepthOption b) (blueDepthList rs) := by
  rw [blueDepth]

theorem redDepth_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    redDepth (node b rs)
      = max (redDepthOption b) (redDepthList rs) := by
  rw [redDepth]

theorem redBranchingLe_node (L : ℕ∞) (b : Option EraseDecodeTree)
    (rs : List EraseDecodeTree) :
    redBranchingLe L (node b rs)
      ↔ redBranchingLeOption L b ∧
          (rs.length : ℕ∞) ≤ L ∧
          redBranchingLeList L rs := by
  rw [redBranchingLe]

end EraseDecodeTree

/-! ### Leaf-count budget theorem (GGR11 Theorem 3.6 for a real tree) -/

open EraseDecodeTree

private theorem one_le_pow_enat {L : ℕ∞} (hL : 1 ≤ L) : ∀ r : ℕ, (1 : ℕ∞) ≤ L ^ r
  | 0 => by simp
  | r + 1 => by
      rw [pow_succ]
      simpa [one_mul] using mul_le_mul' (one_le_pow_enat hL r) hL

private theorem leafCountList_eq_zero_of_redDepthList_le_zero {rs : List EraseDecodeTree}
    (h : redDepthList rs ≤ 0) : leafCountList rs = 0 := by
  cases rs with
  | nil => simp
  | cons t ts =>
      have hpos : 1 ≤ redDepthList (t :: ts) := by
        rw [redDepthList_cons]
        exact le_trans (by omega : 1 ≤ redDepth t + 1) (le_max_left _ _)
      have : (1 : ℕ) ≤ 0 := le_trans hpos h
      omega

private theorem leafCountOption_eq_zero_of_blueDepthOption_le_zero
    {bopt : Option EraseDecodeTree} (h : blueDepthOption bopt ≤ 0) :
    leafCountOption bopt = 0 := by
  cases bopt with
  | none => simp
  | some t =>
      have hpos : 1 ≤ blueDepthOption (some t) := by
        simp [blueDepthOption]
      have : (1 : ℕ) ≤ 0 := le_trans hpos h
      omega

/-- **GGR11 Theorem 3.6, for the concrete Erase-Decode tree.**

If `1 ≤ L`, every node has at most `L` Red children, and every root→leaf path has
at most `b` Blue and `r` Red edges, then the tree has at most
`(b + r choose r) · L ^ r` leaves.

The hypothesis `1 ≤ L` is the natural normalisation `Λ(C,δ) ≥ 1` (a non-empty,
list-decodable code has at least one close codeword); it is also what makes the
Pascal recursion `t(b,r) ≤ t(b-1,r) + L·t(b,r-1)` an *upper* bound. -/
theorem EraseDecodeTree.leafCount_le (L : ℕ∞) (hL : 1 ≤ L) :
    ∀ (t : EraseDecodeTree) (b r : ℕ),
      blueDepth t ≤ b → redDepth t ≤ r → redBranchingLe L t →
      leafCount t ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
  refine EraseDecodeTree.rec
    (motive_1 := fun t =>
      ∀ (b r : ℕ), blueDepth t ≤ b → redDepth t ≤ r → redBranchingLe L t →
        leafCount t ≤ ((b + r).choose r : ℕ∞) * L ^ r)
    (motive_2 := fun bopt =>
      ∀ (b r : ℕ), blueDepthOption bopt ≤ b + 1 → redDepthOption bopt ≤ r →
        redBranchingLeOption L bopt →
        leafCountOption bopt ≤ ((b + r).choose r : ℕ∞) * L ^ r)
    (motive_3 := fun rs =>
      ∀ (b r : ℕ), blueDepthList rs ≤ b → redDepthList rs ≤ r + 1 →
        redBranchingLeList L rs →
        leafCountList rs ≤ (rs.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r))
    ?leaf ?node ?none ?some ?nil ?cons
  · intro b r _ _ _
    simp only [leafCount_leaf]
    have h1 : (1 : ℕ∞) ≤ ((b + r).choose r : ℕ∞) := by
      have : 1 ≤ (b + r).choose r := Nat.choose_pos (Nat.le_add_left r b)
      exact_mod_cast this
    have h2 : (1 : ℕ∞) ≤ L ^ r := one_le_pow_enat hL r
    calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ ((b + r).choose r : ℕ∞) * L ^ r := mul_le_mul' h1 h2
  · intro bopt rs ihb ihrs b r hbd hrd hbr
    rw [redBranchingLe_node] at hbr
    obtain ⟨hbr_blue, hrs_len, hrs_red⟩ := hbr
    rw [blueDepth_node] at hbd
    rw [redDepth_node] at hrd
    rw [leafCount_node]
    cases r with
    | zero =>
        have hred0 : redDepthList rs ≤ 0 := le_trans (le_max_right _ _) hrd
        have hlist0 : leafCountList rs = 0 := leafCountList_eq_zero_of_redDepthList_le_zero hred0
        rw [hlist0, add_zero]
        cases b with
        | zero =>
            have hblue0 : blueDepthOption bopt ≤ 0 := le_trans (le_max_left _ _) hbd
            rw [leafCountOption_eq_zero_of_blueDepthOption_le_zero hblue0]
            simp
        | succ b =>
            have hblue : leafCountOption bopt ≤ ((b + 0).choose 0 : ℕ∞) * L ^ 0 := by
              exact ihb b 0 (le_trans (le_max_left _ _) hbd)
                (le_trans (le_max_left _ _) hrd) hbr_blue
            simpa using hblue
    | succ r =>
        have hsum :
            leafCountList rs ≤ (rs.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) :=
          ihrs b r (le_trans (le_max_right _ _) hbd) (le_trans (le_max_right _ _) hrd)
            hrs_red
        have hsum' : leafCountList rs ≤ L * (((b + r).choose r : ℕ∞) * L ^ r) :=
          le_trans hsum (mul_le_mul' hrs_len (le_refl _))
        cases b with
        | zero =>
            have hblue0 : blueDepthOption bopt ≤ 0 := le_trans (le_max_left _ _) hbd
            rw [leafCountOption_eq_zero_of_blueDepthOption_le_zero hblue0, zero_add]
            calc leafCountList rs
                ≤ L * (((0 + r).choose r : ℕ∞) * L ^ r) := hsum'
              _ = ((0 + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
                  simp [Nat.choose_self, pow_succ]
                  ring
        | succ b =>
            have hblue :
                leafCountOption bopt
                  ≤ ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
              exact ihb b (r + 1) (le_trans (le_max_left _ _) hbd)
                (le_trans (le_max_left _ _) hrd) hbr_blue
            calc leafCountOption bopt + leafCountList rs
                ≤ ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1)
                    + L * ((((b + 1) + r).choose r : ℕ∞) * L ^ r) :=
                  add_le_add hblue hsum'
              _ = (((b + (r + 1)).choose (r + 1) : ℕ∞)
                    + (((b + 1) + r).choose r : ℕ∞)) * L ^ (r + 1) := by
                  ring
              _ = (((b + 1) + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
                  congr 1
                  have hsplit : (b + 1) + (r + 1) = (b + (r + 1)) + 1 := by ring
                  rw [hsplit, Nat.choose_succ_succ (b + (r + 1)) r]
                  push_cast
                  have e1 : b + (r + 1) = b + r + 1 := by ring
                  have e2 : b + 1 + r = b + r + 1 := by ring
                  rw [e1, e2]
                  ring
  · intro b r _ _ _
    simp
  · intro t iht b r hbd hrd hbr
    rw [blueDepthOption_some] at hbd
    rw [redDepthOption_some] at hrd
    rw [redBranchingLeOption_some] at hbr
    rw [leafCountOption_some]
    exact iht b r (by omega) hrd hbr
  · intro b r _ _ _
    simp
  · intro t ts iht ihts b r hbd hrd hbr
    rw [redBranchingLeList_cons] at hbr
    obtain ⟨hbr_t, hbr_ts⟩ := hbr
    rw [blueDepthList_cons] at hbd
    rw [redDepthList_cons] at hrd
    rw [leafCountList_cons]
    have ht : leafCount t ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
      have hrd_t : redDepth t ≤ r := by
        have : redDepth t + 1 ≤ r + 1 := le_trans (le_max_left _ _) hrd
        omega
      exact iht b r (le_trans (le_max_left _ _) hbd) hrd_t hbr_t
    have hts :
        leafCountList ts
          ≤ (ts.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) := by
      exact ihts b r (le_trans (le_max_right _ _) hbd) (le_trans (le_max_right _ _) hrd)
        hbr_ts
    calc leafCount t + leafCountList ts
        ≤ ((b + r).choose r : ℕ∞) * L ^ r
            + (ts.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) :=
          add_le_add ht hts
      _ = ((t :: ts).length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) := by
          simp [Nat.cast_add, add_mul, one_mul, add_comm]

/-! ### Bridge to the abstract residual -/

open Code ListDecodable

variable {ι F : Type} [Fintype ι]

/-- A single concrete Erase-Decode tree supplies the named per-word GGR11 witness.

This is the exact target shape for the future Algorithm-1 construction: once the
algorithm produces a concrete tree whose leaves dominate the close-codeword set
and whose Blue/Red depths and Red branching obey the GGR11 budgets, the closed
Pascal-form leaf-count function satisfies the `GGR11TreeWitness` interface. -/
noncomputable def treeWitness_of_concreteEraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    (f : Matrix ι (Fin m) F) (tree : EraseDecodeTree)
    (hdom :
      (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
          ≤ tree.leafCount)
    (hbd : tree.blueDepth ≤ b) (hrd : tree.redDepth ≤ r)
    (hbr : tree.redBranchingLe (Lambda C δ)) :
    GGR11TreeWitness C δ m b r f := by
  refine
    { leafCount := fun b' r' => ((b' + r').choose r' : ℕ∞) * (Lambda C δ) ^ r'
      close_le_leafCount := ?_
      no_red_budget := ?_
      red_only_step := ?_
      blue_red_step := ?_ }
  · calc (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
          ≤ tree.leafCount := hdom
        _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
            EraseDecodeTree.leafCount_le (Lambda C δ) hL tree b r hbd hrd hbr
  · intro b'; simp
  · intro r'
    simp only [Nat.zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [pow_succ, mul_comm]
  · intro b' r'
    calc ((b' + 1 + (r' + 1)).choose (r' + 1) : ℕ∞) * (Lambda C δ) ^ (r' + 1)
        = (((b' + (r' + 1)).choose (r' + 1) : ℕ∞)
            + ((b' + (r' + 1)).choose r' : ℕ∞)) * (Lambda C δ) ^ (r' + 1) := by
          congr 1
          have hsplit : b' + 1 + (r' + 1) = (b' + (r' + 1)) + 1 := by ring
          rw [hsplit, Nat.choose_succ_succ (b' + (r' + 1)) r']
          push_cast; ring
      _ = ((b' + (r' + 1)).choose (r' + 1) : ℕ∞) * (Lambda C δ) ^ (r' + 1)
            + ((b' + (r' + 1)).choose r' : ℕ∞) * (Lambda C δ) ^ (r' + 1) := by ring
      _ ≤ ((b' + (r' + 1)).choose (r' + 1) : ℕ∞) * (Lambda C δ) ^ (r' + 1)
            + (Lambda C δ) * (((b' + 1 + r').choose r' : ℕ∞) * (Lambda C δ) ^ r') := by
          refine add_le_add (le_refl _) ?_
          rw [pow_succ]
          have hcast : ((b' + (r' + 1)).choose r' : ℕ∞)
              ≤ ((b' + 1 + r').choose r' : ℕ∞) := by
            have : (b' + (r' + 1)).choose r' = (b' + 1 + r').choose r' := by
              congr 1; omega
            exact le_of_eq (by exact_mod_cast this)
          calc ((b' + (r' + 1)).choose r' : ℕ∞) * ((Lambda C δ) ^ r' * (Lambda C δ))
              = (Lambda C δ) * (((b' + (r' + 1)).choose r' : ℕ∞) * (Lambda C δ) ^ r') := by
                ring
            _ ≤ (Lambda C δ) * (((b' + 1 + r').choose r' : ℕ∞) * (Lambda C δ) ^ r') :=
                mul_le_mul' (le_refl _) (mul_le_mul' hcast (le_refl _))

/-- Concrete Erase-Decode tree existence supplies the named per-word GGR11 witness.

This is the one-word construction target for the remaining Algorithm-1 work: produce a concrete
tree whose leaves dominate the close codewords and whose Blue/Red depths and Red branching meet
the GGR11 budgets. The closed-form witness data is then fully internal. -/
theorem treeWitness_of_eraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    {f : Matrix ι (Fin m) F}
    (H : ∃ t : EraseDecodeTree,
      (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
          ≤ t.leafCount ∧
      t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    Nonempty (GGR11TreeWitness C δ m b r f) := by
  obtain ⟨tree, hdom, hbd, hrd, hbr⟩ := H
  exact ⟨treeWitness_of_concreteEraseDecodeTree hL f tree hdom hbd hrd hbr⟩

/-- **Constructive witness for `GGR11TreeStructure`.**

Suppose for every received word `f` there is an Erase-Decode tree (with red
branching `≤ Λ(C,δ)`, blue depth `≤ b`, red depth `≤ r`) whose leaf count
dominates the close-codeword set, and `1 ≤ Λ(C,δ)`.  Then the abstract residual
`GGR11TreeStructure` holds.

This exhibits the abstract leaf-count function `t` as the closed-form GGR11 bound
applied to the *actual* tree, so the residual is no longer an unwitnessed `∃ t`;
the only thing still external is producing the trees themselves. -/
theorem treeStructure_of_eraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    (H : ∀ f : Matrix ι (Fin m) F,
      ∃ t : EraseDecodeTree,
        (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
            ≤ t.leafCount ∧
        t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    GGR11TreeStructure C δ m b r := by
  intro f
  obtain ⟨w⟩ := treeWitness_of_eraseDecodeTree hL (H f)
  exact ⟨w.leafCount, w.close_le_leafCount, w.no_red_budget, w.red_only_step, w.blue_red_step⟩

/-- Concrete Erase-Decode trees supply the named GGR11 tree frontier. This is the granular
frontier form of `treeStructure_of_eraseDecodeTree`, useful for downstream code that wants the
per-word witness interface rather than the older anonymous residual. -/
theorem treeFrontier_of_eraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    (H : ∀ f : Matrix ι (Fin m) F,
      ∃ t : EraseDecodeTree,
        (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
            ≤ t.leafCount ∧
        t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    GGR11TreeFrontier C δ m b r := by
  intro f
  exact treeWitness_of_eraseDecodeTree hL (H f)

/-- Concrete Erase-Decode trees discharge the per-word GGR11 list-size bound. -/
theorem perWordBound_of_eraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    (H : ∀ f : Matrix ι (Fin m) F,
      ∃ t : EraseDecodeTree,
        (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
            ≤ t.leafCount ∧
        t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    GGR11PerWordBound C δ m b r :=
  perWordBound_of_treeFrontier (treeFrontier_of_eraseDecodeTree hL H)

/-- End-to-end interleaved list-size bound from concrete Erase-Decode trees. -/
theorem lambda_le_ggr11_of_eraseDecodeTree
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} (hL : 1 ≤ Lambda C δ)
    (H : ∀ f : Matrix ι (Fin m) F,
      ∃ t : EraseDecodeTree,
        (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin m) C) f δ).encard
            ≤ t.leafCount ∧
        t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    Lambda (Code.interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_treeFrontier (treeFrontier_of_eraseDecodeTree hL H)

-- Axiom audit.
#print axioms EraseDecodeTree.leafCount_le
#print axioms treeWitness_of_concreteEraseDecodeTree
#print axioms treeWitness_of_eraseDecodeTree
#print axioms treeStructure_of_eraseDecodeTree
#print axioms treeFrontier_of_eraseDecodeTree
#print axioms perWordBound_of_eraseDecodeTree
#print axioms lambda_le_ggr11_of_eraseDecodeTree

end InterleavedCode.GGR11
