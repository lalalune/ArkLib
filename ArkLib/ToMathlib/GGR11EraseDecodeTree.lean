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

/-- Number of leaves of an Erase-Decode tree (as `ℕ∞`, so it composes with the
`Lambda`-valued budgets).  A leaf contributes `1`; an internal node sums its Blue
subtree (if present) and all its Red subtrees. -/
def leafCount : EraseDecodeTree → ℕ∞
  | leaf => 1
  | node b rs => (b.elim 0 fun t => t.leafCount) + (rs.attach.map fun t => t.1.leafCount).sum
decreasing_by
  · cases b with
    | none => simp at *
    | some t => simp_all; omega
  · exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem t.2) (by simp; omega)

/-- Maximum number of Blue edges on any root→leaf path. -/
def blueDepth : EraseDecodeTree → ℕ
  | leaf => 0
  | node b rs =>
      max (b.elim 0 fun t => t.blueDepth + 1)
        ((rs.attach.map fun t => t.1.blueDepth).foldr max 0)
decreasing_by
  · cases b with
    | none => simp at *
    | some t => simp_all; omega
  · exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem t.2) (by simp; omega)

/-- Maximum number of Red edges on any root→leaf path. -/
def redDepth : EraseDecodeTree → ℕ
  | leaf => 0
  | node b rs =>
      max (b.elim 0 fun t => t.redDepth)
        ((rs.attach.map fun t => t.1.redDepth + 1).foldr max 0)
decreasing_by
  · cases b with
    | none => simp at *
    | some t => simp_all; omega
  · exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem t.2) (by simp; omega)

/-- `redBranchingLe L t`: every node of `t` has at most `L` Red children. -/
def redBranchingLe (L : ℕ∞) : EraseDecodeTree → Prop
  | leaf => True
  | node b rs =>
      (b.elim True fun t => redBranchingLe L t) ∧
      (rs.length : ℕ∞) ≤ L ∧
      (∀ t ∈ rs.attach, redBranchingLe L t.1)
decreasing_by
  · cases b with
    | none => simp at *
    | some t => simp_all; omega
  · exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem t.2) (by simp; omega)

@[simp] theorem leafCount_leaf : leafCount leaf = 1 := rfl

@[simp] theorem blueDepth_leaf : blueDepth leaf = 0 := rfl

@[simp] theorem redDepth_leaf : redDepth leaf = 0 := rfl

theorem leafCount_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    leafCount (node b rs)
      = (b.elim 0 fun t => t.leafCount) + (rs.attach.map fun t => t.1.leafCount).sum := by
  rw [leafCount]

theorem blueDepth_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    blueDepth (node b rs)
      = max (b.elim 0 fun t => t.blueDepth + 1)
          ((rs.attach.map fun t => t.1.blueDepth).foldr max 0) := by
  rw [blueDepth]

theorem redDepth_node (b : Option EraseDecodeTree) (rs : List EraseDecodeTree) :
    redDepth (node b rs)
      = max (b.elim 0 fun t => t.redDepth)
          ((rs.attach.map fun t => t.1.redDepth + 1).foldr max 0) := by
  rw [redDepth]

theorem redBranchingLe_node (L : ℕ∞) (b : Option EraseDecodeTree)
    (rs : List EraseDecodeTree) :
    redBranchingLe L (node b rs)
      ↔ (b.elim True fun t => redBranchingLe L t) ∧
          (rs.length : ℕ∞) ≤ L ∧
          (∀ t ∈ rs.attach, redBranchingLe L t.1) := by
  rw [redBranchingLe]

end EraseDecodeTree

/-! ### A `foldr max` helper -/

/-- A member of a `List ℕ` is `≤` its `foldr max 0`. -/
theorem le_foldr_max : ∀ (l : List ℕ) (n : ℕ), n ∈ l → n ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro n hn; simp at hn
  | cons a t ih =>
      intro n hn
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 hn with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih n h) (le_max_right _ _)

/-! ### Leaf-count budget theorem (GGR11 Theorem 3.6 for a real tree) -/

open EraseDecodeTree

/-- Monotonicity of the closed-form GGR11 bound in the Blue budget `b`. -/
private theorem ggr11Bound_mono_blue (L : ℕ∞) {b b' r : ℕ} (h : b ≤ b') :
    ((b + r).choose r : ℕ∞) * L ^ r ≤ ((b' + r).choose r : ℕ∞) * L ^ r := by
  gcongr
  exact_mod_cast Nat.choose_le_choose r (by omega)

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
      leafCount t ≤ ((b + r).choose r : ℕ∞) * L ^ r
  | leaf, b, r, _, _, _ => by
      simp only [leafCount_leaf]
      have h1 : (1 : ℕ∞) ≤ ((b + r).choose r : ℕ∞) := by
        have : 1 ≤ (b + r).choose r := Nat.choose_pos (Nat.le_add_left r b)
        exact_mod_cast this
      have h2 : (1 : ℕ∞) ≤ L ^ r := one_le_pow_of_le' hL r
      calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ ((b + r).choose r : ℕ∞) * L ^ r := mul_le_mul' h1 h2
  | node bopt rs, b, r, hbd, hrd, hbr => by
      rw [redBranchingLe_node] at hbr
      obtain ⟨hbr_blue, hrs_len, hrs_red⟩ := hbr
      rw [blueDepth_node] at hbd
      rw [redDepth_node] at hrd
      -- Blue subtree bound.
      have hblue :
          (bopt.elim 0 fun t => t.leafCount) ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
        cases bopt with
        | none => simp
        | some t =>
            simp only [Option.elim] at hbd hrd hbr_blue ⊢
            have hb_t : t.blueDepth + 1 ≤ b := le_trans (le_max_left _ _) hbd
            have hr_t : t.redDepth ≤ r := le_trans (le_max_left _ _) hrd
            obtain ⟨b'', rfl⟩ : ∃ b'', b = b'' + 1 := ⟨b - 1, by omega⟩
            have hbd_t : t.blueDepth ≤ b'' := by omega
            have hsub := EraseDecodeTree.leafCount_le L hL t b'' r hbd_t hr_t hbr_blue
            calc t.leafCount ≤ ((b'' + r).choose r : ℕ∞) * L ^ r := hsub
              _ ≤ (((b'' + 1) + r).choose r : ℕ∞) * L ^ r :=
                  ggr11Bound_mono_blue L (by omega)
      -- Now case on the Red budget.
      rw [leafCount_node]
      cases r with
      | zero =>
          -- No Red budget ⇒ no Red children.
          have hrs_nil : rs = [] := by
            by_contra hne
            obtain ⟨t, htmem⟩ := List.exists_mem_of_ne_nil rs hne
            have hpos : 1 ≤ (rs.attach.map fun s => s.1.redDepth + 1).foldr max 0 := by
              refine le_trans (by omega : 1 ≤ t.redDepth + 1) ?_
              refine le_foldr_max _ _ ?_
              exact List.mem_map.2 ⟨⟨t, htmem⟩, List.mem_attach _ _, rfl⟩
            have := le_trans hpos (le_trans (le_max_right _ _) hrd)
            omega
          subst hrs_nil
          simp only [List.attach_nil, List.map_nil, List.sum_nil, add_zero,
            Nat.add_zero, Nat.choose_self, Nat.cast_one, pow_zero, mul_one]
          simpa using hblue
      | succ r =>
          -- Each red subtree: blueDepth ≤ b, redDepth ≤ r.
          have hred_each : ∀ t ∈ rs.attach,
              t.1.leafCount ≤ ((b + r).choose r : ℕ∞) * L ^ r := by
            intro t htmem
            have htmem' : t.1 ∈ rs := t.2
            have hbd_t : t.1.blueDepth ≤ b := by
              refine le_trans ?_ (le_trans (le_max_right _ _) hbd)
              exact le_foldr_max _ _ (List.mem_map.2 ⟨t, List.mem_attach _ _, rfl⟩)
            have hrd_t : t.1.redDepth ≤ r := by
              have hmem : t.1.redDepth + 1 ∈
                  rs.attach.map fun s => s.1.redDepth + 1 :=
                List.mem_map.2 ⟨t, List.mem_attach _ _, rfl⟩
              have := le_trans (le_foldr_max _ _ hmem)
                (le_trans (le_max_right _ _) hrd)
              omega
            exact EraseDecodeTree.leafCount_le L hL t.1 b r hbd_t hrd_t
              (hrs_red t htmem)
          -- Sum of red leaf counts ≤ L · (b+r choose r)·L^r.
          have hsum :
              (rs.attach.map fun t => t.1.leafCount).sum ≤
                (rs.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) := by
            calc (rs.attach.map fun t => t.1.leafCount).sum
                ≤ (rs.attach.map fun _ => ((b + r).choose r : ℕ∞) * L ^ r).sum := by
                  apply List.sum_le_sum_of_mem_le
                  intro x hx
                  simp only [List.mem_map] at hx
                  obtain ⟨t, htmem, rfl⟩ := hx
                  exact hred_each t htmem
              _ = (rs.length : ℕ∞) * (((b + r).choose r : ℕ∞) * L ^ r) := by
                  rw [List.map_const', List.sum_replicate, List.length_attach,
                    nsmul_eq_mul]
          have hsum' :
              (rs.attach.map fun t => t.1.leafCount).sum
                ≤ L * (((b + r).choose r : ℕ∞) * L ^ r) :=
            le_trans hsum (mul_le_mul' hrs_len (le_refl _))
          calc (bopt.elim 0 fun t => t.leafCount)
                + (rs.attach.map fun t => t.1.leafCount).sum
              ≤ ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1)
                  + L * (((b + r).choose r : ℕ∞) * L ^ r) := add_le_add hblue hsum'
            _ = ((b + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1)
                  + ((b + r).choose r : ℕ∞) * L ^ (r + 1) := by ring
            _ ≤ (((b + 1) + (r + 1)).choose (r + 1) : ℕ∞) * L ^ (r + 1) := by
                rw [← add_mul]
                refine mul_le_mul' ?_ (le_refl _)
                have hkey :
                    (b + (r + 1)).choose (r + 1) + (b + r).choose r
                      = ((b + 1) + (r + 1)).choose (r + 1) := by
                  have hsplit : (b + 1) + (r + 1) = (b + (r + 1)) + 1 := by ring
                  rw [hsplit, Nat.choose_succ_succ (b + (r + 1)) r]
                  have e : (b + r).choose r = (b + (r + 1)).choose r := by
                    congr 1 <;> omega
                  rw [e]; ring
                exact_mod_cast hkey.le
  termination_by t _ _ _ _ _ => sizeOf t
  decreasing_by
    · simp_wf; omega
    · simp_wf
      have := List.sizeOf_lt_of_mem t.2
      omega

/-! ### Bridge to the abstract residual -/

variable {ι F : Type} [Fintype ι]

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
        (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
            ≤ t.leafCount ∧
        t.blueDepth ≤ b ∧ t.redDepth ≤ r ∧ t.redBranchingLe (Lambda C δ)) :
    GGR11TreeStructure C δ m b r := by
  intro f
  obtain ⟨tree, hdom, hbd, hrd, hbr⟩ := H f
  refine ⟨fun b' r' => ((b' + r').choose r' : ℕ∞) * (Lambda C δ) ^ r', ?_, ?_, ?_, ?_⟩
  · calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
          ≤ tree.leafCount := hdom
        _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
            EraseDecodeTree.leafCount_le (Lambda C δ) hL tree b r hbd hrd hbr
  · intro b'; simp
  · intro r'
    simp only [Nat.zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [pow_succ, mul_comm]
  · intro b' r'
    simp only
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

-- Axiom audit.
#print axioms EraseDecodeTree.leafCount_le
#print axioms treeStructure_of_eraseDecodeTree

end InterleavedCode.GGR11
