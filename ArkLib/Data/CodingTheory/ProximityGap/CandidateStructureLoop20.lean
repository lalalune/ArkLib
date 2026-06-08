/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Loop 20 — the smooth domain's RS automorphism group acts on the close-codeword list

Loop 19 showed the smooth domain `L = μ_N` (`N`-th roots of unity) is the root set of the sparse
`X^N − 1`, with a large symmetry group. This file formalizes the *code* consequence: scaling the
argument by a root of unity `ω` is a **Reed–Solomon code automorphism** — it preserves the
degree-`<k` bound, hence maps `RS[k]` to `RS[k]` and permutes the smooth domain `μ_N`.

So the multiplicative group `μ_N` (order `N = 2^m`) acts on `RS[k]` over the smooth domain. Composed
with the Loop 6 orbit machinery this gives the symmetry mechanism for the **disproof side** of the
Loop 18 decision: the close-codeword list of a received word `r` is permuted by the stabilizer of
`r`, so a free orbit of a close codeword forces the list `≥ orbit size`.

**Honest both-ways analysis (the reason this neither proves nor disproves).** The mechanism cuts both
ways, exactly mirroring the smooth-vs-generic tension:
* *Disproof lean.* A non-trivially-symmetric received word with a free-orbit close codeword would have
  list `≥` (orbit size, up to `N`) — super-polynomial ⇒ prize FALSE (Loop8).
* *Proof lean.* But the *full* group `μ_N` acts **transitively** on `L`, so a fully-`μ_N`-invariant
  word is **constant** on `L`, and below capacity a constant word's only close codeword is the
  constant itself (its `p − γ` has `> k` roots ⇒ `p = γ`) — list size `1`, no explosion. Forcing a
  large free orbit needs an intermediate subgroup `μ_d` (`d ∣ N`) balancing symmetry against
  transitivity; whether such a balance is realizable at the prize radius is precisely the open
  question.

This file proves the automorphism (scaling preserves the degree bound), sorry-free and axiom-clean;
the orbit lower bound is `DisproofLoop6.frobenius_orbit_card_le` reused with `σ : x ↦ ωx`. See
`DISPROOF_LOG.md` (Loop20).
-/

namespace ArkLib.ProximityGap.StructureLoop20

open Polynomial

variable {F : Type*} [Field F]

/-- **Scaling is an RS code automorphism (degree-bound preservation).** For `ω ≠ 0` and a polynomial
`p` of degree `< k`, the scaled polynomial `p(ω·X) = p.comp (C ω * X)` also has degree `< k`. Hence
`x ↦ p(ω·x)` is again a codeword of `RS[k]`, so multiplication-by-`ω` permutes `RS[k]`. -/
theorem scaling_preserves_degreeLT {p : F[X]} {k : ℕ} {ω : F}
    (hp : p.natDegree < k) :
    (p.comp (C ω * X)).natDegree < k := by
  have hle : (p.comp (C ω * X)).natDegree ≤ p.natDegree * (C ω * X).natDegree :=
    natDegree_comp_le
  have hlin : (C ω * X : F[X]).natDegree ≤ 1 := by
    calc (C ω * X : F[X]).natDegree ≤ (C ω).natDegree + X.natDegree := natDegree_mul_le
      _ ≤ 0 + 1 := by gcongr <;> simp [natDegree_C, natDegree_X]
      _ = 1 := by ring
  calc (p.comp (C ω * X)).natDegree ≤ p.natDegree * (C ω * X).natDegree := hle
    _ ≤ p.natDegree * 1 := by gcongr
    _ = p.natDegree := mul_one _
    _ < k := hp

/-- **Iterated scaling stays in `RS[k]`.** Repeated scaling by `ω` (the `μ_N` action) keeps the
degree below `k`, so the whole `μ_N`-orbit of a codeword lies in `RS[k]`. (Degree-bound preservation
is closed under composition — the substance of "`μ_N` acts on `RS[k]`".) -/
theorem scaling_iterate_preserves_degreeLT {p : F[X]} {k : ℕ} {ω : F}
    (hp : p.natDegree < k) (j : ℕ) :
    (Nat.rec p (fun _ q => q.comp (C ω * X)) j).natDegree < k := by
  induction j with
  | zero => simpa using hp
  | succ n ih => exact scaling_preserves_degreeLT ih

end ArkLib.ProximityGap.StructureLoop20
