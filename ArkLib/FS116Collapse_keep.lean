import ArkLib.OracleReduction.LiftContext.Reduction

/-! #116B helper: the empty-oracle leaf-collapse, PROVEN (no sorry). NOT in build.
`OptionT.run (liftM X)` is defeq `liftComp (some <$> X)` (cf. NoInteraction.reduction_completeness),
so simulating under `impl + implC` drops the unqueried second oracle. -/
noncomputable section
open OracleComp OracleSpec

variable {ι κ : Type} {spec₁ : OracleSpec ι} {specC : OracleSpec κ} {α σ : Type}
  [MonadLiftT (OracleComp spec₁) (OracleComp (spec₁ + specC))]

theorem leaf_collapse
    (impl : QueryImpl spec₁ (StateT σ ProbComp))
    (implC : QueryImpl specC (StateT σ ProbComp))
    (X : OracleComp spec₁ α) :
    simulateQ (impl + implC) ((monadLift X : OptionT (OracleComp (spec₁ + specC)) α).run)
      = some <$> simulateQ impl X := by
  have h : (monadLift X : OptionT (OracleComp (spec₁ + specC)) α).run
        = OracleComp.liftComp (some <$> X) (spec₁ + specC) := rfl
  rw [h, QueryImpl.simulateQ_add_liftComp_left, simulateQ_map]
