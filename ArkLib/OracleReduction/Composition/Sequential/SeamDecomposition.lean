/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Malicious-prover seam decomposition for `pSpec₁ ++ₚ pSpec₂` (issue #13 / #25)

The soundness composition theorem `Verifier.append_soundness` (in `Append.lean`) is residual-gated
on `appendSoundnessResidual`, whose stated obstruction is:

> soundness quantifies over an *arbitrary malicious* prover `P` over `pSpec₁ ++ₚ pSpec₂`, so the
> proof must decompose `P` at the seam round `m` into a `pSpec₁`-phase malicious prover `P↾₁`
> (running rounds `0..m-1`, with `P`'s round-`m` output context as its `output`) and a `pSpec₂`-phase
> malicious prover `P↾₂` (resuming from that context). … no analogue of the honest `Prover.append`
> exists in the codebase yet.

This file supplies exactly that missing construction: `Prover.fst` (the `P↾₁` left half) and
`Prover.snd` (the `P↾₂` right half).  They are the inverse of the honest `Prover.append`: where
`Prover.append` glues two provers into one over the appended protocol, `fst`/`snd` *split* an
arbitrary prover over the appended protocol back into its two phases, carrying `P`'s seam state
(its `PrvState` at the last `pSpec₁` round) across the cut.

* `Prover.fst P : Prover … Stmt₁ Wit₁ (P.PrvState ⟨m⟩) Unit pSpec₁` — runs rounds `0..m-1` exactly
  as `P`, then outputs the seam state.
* `Prover.snd P : Prover … (P.PrvState ⟨m⟩) Unit Stmt₃ Wit₃ pSpec₂` — resumes from the seam state
  (passed in as the input statement) and runs rounds `m..m+n-1` exactly as `P`, ending with `P`'s
  own output.

The constructions reuse the left-/right-half transport lemmas (`append_dir_castLE`/`_natAdd`,
`append_Message_castLE`/`_natAdd`, `append_Challenge_natAdd`) proven in `Append.lean`.  Each round
of a restriction lies wholly in one half of the appended protocol, so — unlike `Prover.append`,
which must case-split on `i < m`, `i = m`, `i > m` — no per-round case analysis is needed.

These are axiom-clean and `sorry`-free.  The remaining steps toward `appendSoundnessResidual` are
the seam-merge identity (`P` agrees with `(Prover.fst P).append (Prover.snd P)` on its run) and the
probabilistic union bound over the intermediate statement; both are documented in `appendSoundness`.
-/

open OracleComp ProtocolSpec OracleVerifier.Append

universe u

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

/-- **Phase-1 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`.
Runs rounds `0 .. m-1` exactly as `P` does, and outputs `P`'s seam state (its `PrvState` at the
last `pSpec₁` round) as the output statement, with trivial output witness. This is the
malicious-prover analogue (left half) absent from the codebase, needed for `appendSoundnessResidual`.
-/
def fst (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec Stmt₁ Wit₁
      (P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m))) Unit pSpec₁ where
  PrvState := fun (i : Fin (m + 1)) =>
    P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) i)
  input := P.input
  sendMessage := fun ⟨i, hDir⟩ state => by
    have hle : m + 1 ≤ m + n + 1 := by omega
    have hmn : m ≤ m + n := by omega
    have hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE hmn i) = .P_to_V := by
      rw [append_dir_castLE]; exact hDir
    have hcs : Fin.castLE hle i.castSucc = (Fin.castLE hmn i).castSucc := by ext; simp
    have hsucc : Fin.castLE hle i.succ = (Fin.castLE hmn i).succ := by ext; simp
    have hMsg : (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.castLE hmn i, hDir'⟩
        = pSpec₁.Message ⟨i, hDir⟩ := append_Message_castLE i hDir' hDir
    refine (fun p => ?_) <$> (P.sendMessage ⟨Fin.castLE hmn i, hDir'⟩ (hcs ▸ state))
    exact (cast hMsg p.1, hsucc ▸ p.2)
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    have hle : m + 1 ≤ m + n + 1 := by omega
    have hmn : m ≤ m + n := by omega
    have hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE hmn i) = .V_to_P := by
      rw [append_dir_castLE]; exact hDir
    have hcs : Fin.castLE hle i.castSucc = (Fin.castLE hmn i).castSucc := by ext; simp
    have hsucc : Fin.castLE hle i.succ = (Fin.castLE hmn i).succ := by ext; simp
    have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.castLE hmn i, hDir'⟩
        = pSpec₁.Challenge ⟨i, hDir⟩ := by
      show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castLE hmn i) = pSpec₁.«Type» i
      rw [Fin.vappend_eq_append,
        show (Fin.castLE hmn i) = Fin.castAdd n i from by ext; simp, Fin.append_left]
    refine (fun f => ?_) <$> (P.receiveChallenge ⟨Fin.castLE hmn i, hDir'⟩ (hcs ▸ state))
    intro c
    exact hsucc ▸ (f (cast hChal.symm c))
  output := fun state => pure (state, ())

/-- **Phase-2 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`.
Resumes from `P`'s seam state (supplied as the input statement) and runs rounds `m .. m+n-1`
exactly as `P` does, ending with `P`'s own output. The input witness is trivial. Together with
`Prover.fst` this is the malicious-prover seam decomposition needed for `appendSoundnessResidual`. -/
def snd (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec (P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m))) Unit
      Stmt₃ Wit₃ pSpec₂ where
  PrvState := fun (j : Fin (n + 1)) => P.PrvState (Fin.natAdd m j)
  input := fun s => by
    refine cast ?_ s.1
    exact congrArg P.PrvState (by ext; simp)
  sendMessage := fun ⟨k, hDir⟩ state => by
    have hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V := by
      rw [append_dir_natAdd]; exact hDir
    have hcs : Fin.natAdd m k.castSucc = (Fin.natAdd m k).castSucc := by ext; simp
    have hsucc : Fin.natAdd m k.succ = (Fin.natAdd m k).succ := by ext; simp; omega
    have hMsg : (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir'⟩
        = pSpec₂.Message ⟨k, hDir⟩ := append_Message_natAdd k hDir' hDir
    refine (fun p => ?_) <$> (P.sendMessage ⟨Fin.natAdd m k, hDir'⟩ (hcs ▸ state))
    exact (cast hMsg p.1, hsucc ▸ p.2)
  receiveChallenge := fun ⟨k, hDir⟩ state => by
    have hDir' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P := by
      rw [append_dir_natAdd]; exact hDir
    have hcs : Fin.natAdd m k.castSucc = (Fin.natAdd m k).castSucc := by ext; simp
    have hsucc : Fin.natAdd m k.succ = (Fin.natAdd m k).succ := by ext; simp; omega
    have hChal : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir'⟩
        = pSpec₂.Challenge ⟨k, hDir⟩ := append_Challenge_natAdd k hDir' hDir
    refine (fun f => ?_) <$> (P.receiveChallenge ⟨Fin.natAdd m k, hDir'⟩ (hcs ▸ state))
    intro c
    exact hsucc ▸ (f (cast hChal.symm c))
  output := fun state => by
    have hlast : Fin.natAdd m (Fin.last n) = Fin.last (m + n) := by ext; simp
    exact P.output (hlast ▸ state)

end Prover
