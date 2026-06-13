/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCombinatorial

/-!
# Lovett's GM-MDS proof: `V*(k)` is preserved under coordinate reduction (#389)

The combinatorial half of Lovett's inductive step (arXiv:1803.02523).  Layer 5
(`LovettReduction`) transfers *linear independence* across the peel
`P(k,V) ↔ (x − aⱼ)·P(k−1, V−eⱼ)`; this file supplies the matching *hypothesis* the
induction needs: that the reduced system is still a `V*(·)` system, one level down.

> **`isVStar_reduce`** — if `V` satisfies `V*(k)` and some coordinate `j` has `Vᵢ(j) ≥ 1`
> for **every** `i` (i.e. the global meet has `meet(j) ≥ 1`, the case where the whole family
> peels `(x − aⱼ)`), then the reduced system `V' = (Function.update Vᵢ j (Vᵢ(j) − 1))ᵢ`
> satisfies `V*(k − 1)`.

The three `IsVStar` clauses each drop by exactly one under the peel: weights `|Vᵢ|` and the
meet weight `|⋀Vᵢ|` each lose `1` (coordinate `j` lowered), `k` loses `1`, so clause (i)
`|Vᵢ| ≤ k−1` and the clause-(ii) MDS inequality are preserved verbatim, and clause (iii)
(the `{0,1}`-except-last shape) only shrinks coordinate `j`.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- The reduced system: lower coordinate `j` of every vector by one. -/
def vReduce (V : Fin m → (Fin n → ℕ)) (j : Fin n) : Fin m → (Fin n → ℕ) :=
  fun i => Function.update (V i) j (V i j - 1)

/-- Lowering coordinate `j` by one (when it is `≥ 1`) drops the weight by exactly one. -/
theorem vAbs_update_pred {v : Fin n → ℕ} {j : Fin n} (hj : 1 ≤ v j) :
    vAbs (Function.update v j (v j - 1)) = vAbs v - 1 := by
  classical
  have key : vAbs (Function.update v j (v j - 1)) + 1 = vAbs v := by
    unfold vAbs
    have e1 : ∑ i, Function.update v j (v j - 1) i
        = (v j - 1) + ∑ i ∈ Finset.univ.erase j, v i := by
      rw [← Finset.add_sum_erase Finset.univ (Function.update v j (v j - 1))
            (Finset.mem_univ j), Function.update_self]
      congr 1
      exact Finset.sum_congr rfl
        (fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _)
    have e2 : ∑ i, v i = v j + ∑ i ∈ Finset.univ.erase j, v i :=
      (Finset.add_sum_erase Finset.univ v (Finset.mem_univ j)).symm
    rw [e1, e2]; omega
  omega

/-- The meet of the reduced family equals the reduction of the meet: only coordinate `j`
changes, and there by `−1` (valid because every `Vᵢ(j) ≥ 1`, so the inf over `j` is `≥ 1`). -/
theorem vMeet_vReduce {V : Fin m → (Fin n → ℕ)} {j : Fin n} (I : Finset (Fin m))
    (hI : I.Nonempty) (hj : ∀ i, 1 ≤ V i j) :
    vMeet (vReduce V j) I hI
      = Function.update (vMeet V I hI) j (vMeet V I hI j - 1) := by
  classical
  funext l
  by_cases hlj : l = j
  · subst hlj
    rw [Function.update_self]
    unfold vMeet vReduce
    simp only [Function.update_self]
    -- `subst` eliminated `j`; coordinate is now `l`. inf'(Vᵢl − 1) = inf'(Vᵢl) − 1.
    refine le_antisymm ?_ ?_
    · obtain ⟨i₁, hi₁, hval⟩ := Finset.exists_mem_eq_inf' hI (fun i => V i l)
      have hle := Finset.inf'_le (fun i => V i l - 1) hi₁
      omega
    · refine Finset.le_inf' _ _ (fun i hi => ?_)
      have : I.inf' hI (fun i => V i l) ≤ V i l := Finset.inf'_le _ hi
      omega
  · rw [Function.update_of_ne hlj]
    unfold vMeet vReduce
    simp only [Function.update_of_ne hlj]

/-- **`V*(k)` is preserved under coordinate reduction.**  If `V` satisfies `V*(k)` and the
global meet has `meet(j) ≥ 1` (every `Vᵢ(j) ≥ 1`), then the reduced system `vReduce V j`
satisfies `V*(k − 1)`. -/
theorem isVStar_reduce {V : Fin m → (Fin n → ℕ)} {k : ℕ} {j : Fin n}
    (hk : 1 ≤ k) (hV : IsVStar V k) (hj : ∀ i, 1 ≤ V i j) :
    IsVStar (vReduce V j) (k - 1) where
  weight_le i := by
    have := hV.weight_le i
    rw [vReduce, vAbs_update_pred (hj i)]
    omega
  mds I hI := by
    have hmds := hV.mds I hI
    -- meet weight drops by one
    have hmeetj : 1 ≤ vMeet V I hI j := by
      unfold vMeet
      exact Finset.le_inf' _ _ (fun i _ => hj i)
    have hmw : vAbs (vMeet (vReduce V j) I hI) = vAbs (vMeet V I hI) - 1 := by
      rw [vMeet_vReduce I hI hj, vAbs_update_pred hmeetj]
    -- one coordinate ≤ the weight, so |meet| ≥ meet(j) ≥ 1 justifies the −1
    have hmle : vMeet V I hI j ≤ vAbs (vMeet V I hI) :=
      Finset.single_le_sum (f := vMeet V I hI) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [hmw]
    -- each summand (k-1) - |V'ᵢ| = k - |Vᵢ|
    have hsum : ∑ i ∈ I, ((k - 1) - vAbs (vReduce V j i))
        = ∑ i ∈ I, (k - vAbs (V i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hwi := hV.weight_le i
      have hji := hj i
      have hjle : V i j ≤ vAbs (V i) :=
        Finset.single_le_sum (f := V i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [vReduce, vAbs_update_pred (hj i)]
      omega
    rw [hsum]
    -- meet weight ≥ 1, so the whole LHS was ≥ 1; original ≤ k gives reduced ≤ k-1
    omega
  shape i l hl := by
    rw [vReduce]
    by_cases hlj : l = j
    · subst hlj
      rw [Function.update_self]
      have := hV.shape i l hl
      omega
    · rw [Function.update_of_ne hlj]; exact hV.shape i l hl

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.isVStar_reduce
