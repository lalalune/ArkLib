

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
  # Equivalence / Isomorphism of Oracle Reductions

  We define observational equivalence between provers and verifiers in an I(O)R.

  We also define equivalence between IORs, in the sense that the statements and witnesses are
  equivalent, and their mapping commute with the reduction (both for the prover and the verifier).

  NOTE: this is now a special case of `liftContext`

  -----------------------------------------------------------------------------------------------

  We will also need to convert between specification and executable models.

  In the best case, we have an isomorphism of the datatypes, which also intertwines with the
  implementation of the prover & verifier.

  However, we may need to deal with more complicated situation. For instance, can we transfer
  results between minor modifications to the protocol? What about when the isomorphism is not exact?

  For the simplest case, it seems we want the following:

  - Assume we have an I(O)R (i.e. the abstract specification): from `RIn₁ : StmtIn₁ × WitIn₁ → Prop`
      to `ROut₁ : StmtOut₁ × WitOut₁ → Prop`.

    We have another I(O)R (i.e. the executable implementation): from `RIn₂ : StmtIn₂ × WitIn₂ →
      Prop` to `ROut₂ : StmtOut₂ × WitOut₂ → Prop`.

    Assume there are mappings in opposite directions:
    `f{Stmt/Wit}{In/Out}₁ : {Stmt/Wit}{In/Out}₁ → {Stmt/Wit}{In/Out}₂` &
    `g{Stmt/Wit}{In/Out}₂ : {Stmt/Wit}{In/Out}₂ → {Stmt/Wit}{In/Out}₁`.
    (for IOR, also mappings between the oracle statements)

  - Then we may transfer security properties from the first to the second I(O)R provided that:
    - Under these mappings, the relations are equivalent
    - Under these mappings, the prover & verifier are equivalent

  - Note that we do not need to require `f/g` to form an equivalence, since this may be too
    restrictive in practice (i.e. concrete polynomial datatypes may contain zero-padding of the
    highest coefficients).

-/

-- section Relation

-- variable {Stmt Wit Stmt' Wit' : Type}

-- def Relation.equiv (f : Stmt ≃ Stmt') (g : Wit ≃ Wit')
--     (R : Stmt → Wit → Prop) (R' : Stmt' → Wit' → Prop) : Prop :=
--   ∀ stmt : Stmt, ∀ wit : Wit, R stmt wit ↔ R' (f stmt) (g wit)

-- theorem Relation.equiv_symm (f : Stmt ≃ Stmt') (g : Wit ≃ Wit')
--     (R : Stmt → Wit → Prop) (R' : Stmt' → Wit' → Prop) :
--   Relation.equiv f g R R' ↔ Relation.equiv f.symm g.symm R' R := by
--   simp [Relation.equiv]
--   constructor
--   · intro h
--     intro stmt' wit'
--     simpa using (h (f.symm stmt') (g.symm wit')).symm
--   · intro h
--     intro stmt wit
--     simpa using (h (f stmt) (g wit)).symm

-- end Relation

namespace ProtocolSpec

-- #check Equiv.instEquivLike

/-- Two protocol specifications are equivalent if they have the same number of rounds, same
  direction for each round, and an equivalence of types for each round. -/
@[ext]
structure Equiv {m n : ℕ} (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) where
  round_eq : m = n
  dir_eq : ∀ i, pSpec.dir i = pSpec'.dir (Fin.cast round_eq i)
  typeEquiv : ∀ i, pSpec.«Type» i ≃ pSpec'.«Type» (Fin.cast round_eq i)

namespace Equiv

-- Note: this is not quite an `EquivLike` since `pSpec`s are terms, not types

variable {m n k : ℕ} {pSpec : ProtocolSpec m} {pSpec' : ProtocolSpec n} {pSpec'' : ProtocolSpec k}

@[simps]
def refl (pSpec : ProtocolSpec n) : Equiv pSpec pSpec where
  round_eq := rfl
  dir_eq := fun _ => rfl
  typeEquiv := fun _ => _root_.Equiv.refl _

def symm (eqv : Equiv pSpec pSpec') : Equiv pSpec' pSpec where
  round_eq := eqv.round_eq.symm
  dir_eq := fun i => by simp [eqv.dir_eq]
  typeEquiv := fun i => (eqv.typeEquiv (Fin.cast (eqv.round_eq.symm) i)).symm

/-- Compose protocol specification equivalences
    (spelled `equivTrans` because `trans` is reserved). -/
def equivTrans (eqv : Equiv pSpec pSpec') (eqv' : Equiv pSpec' pSpec'') : Equiv pSpec pSpec'' where
  round_eq := eqv.round_eq.trans eqv'.round_eq
  dir_eq := fun i => by simp [eqv.dir_eq, eqv'.dir_eq]
  typeEquiv := fun i =>
    _root_.Equiv.trans (eqv.typeEquiv i) (eqv'.typeEquiv (Fin.cast eqv.round_eq i))

end Equiv


end ProtocolSpec

/- Note:

1. Specify equivalence of transcripts, provers, verifiers, reductions
2. Prove distributional equivalence of execution semantics
3. Prove preservation of security properties
-/

variable {n : ℕ} {pSpec pSpec' : ProtocolSpec n}

-- More targeted / limited version of equivalence only for the context, i.e.
-- `ctxEquiv`, `stmtEquiv`, `oStmtEquiv`, `witEquiv`

-- Also, equality and not just equivalence. many times we want observational **equality**. have to
-- specify fewer things

-- Finally, could we go for a general _simulation_ relation?

-- structure Prover.ObsEquiv (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut)
--     (P' : Prover pSpec' oSpec' StmtIn' WitIn' StmtOut' WitOut') where
--   pSpecDirEq : ∀ i, (pSpec i).1 = (pSpec' i).1
--   pSpecEquiv : ∀ i, (pSpec i).2 ≃ (pSpec' i).2
--   stmtInEquiv : StmtIn ≃ StmtIn'
--   witInEquiv : WitIn ≃ WitIn'
--   stmtOutEquiv : StmtOut ≃ StmtOut'
--   witOutEquiv : WitOut ≃ WitOut'
  -- All prover functions give the same output
  -- proverEquiv : ∀ stmtIn witIn, ...

namespace Reduction



end Reduction
