# ArkLib Residual Census (auto-generated, v2)

Accurate classification of every named `*Residual : Prop`. Discharge detection covers
`*_holds`, `*_proved`, `*_canonical_proved`, `*_unconditional` theorems, `*_of_*` reductions,
and theorems whose stated conclusion *is* the residual. **The 'named residual' convention is a
modularity pattern, not an incompleteness marker.**

- **Total named residuals:** 103
- **DISCHARGED** (closed unconditionally): 37
- **REDUCED** (closed conditional on a named deeper hypothesis): 25
- **DEEP-OPEN** (genuine research obligation): 41

## DEEP-OPEN — the genuine remaining mathematics

Categories (all require focused, often multi-session, work):
- **§5.6→§5.8 hybrid couplings**: `Hyb01/12/23/34StepResidual`, `Lemma5_12/14/16HonestResidual`,
  `KeyLemma*Residual`, `SimulatedProver*BudgetResidual`, `D2*BudgetResidual`. The generic
  failing-game TV-coupling toolkit (`ArkLib/ToVCVio/SPMFCoupling.lean`) is landed; each reduces
  to its 3 game-coincidence facts, the hard one being `h_eq` (CO25 Lemma 5.9 carrier coupling).
- **BCIKS20 ProximityGap / coding theory**: `*CoeffPolys*`, `*FaaDiBruno*`, `GKL24*`,
  `BoundaryCard*`, `RIMFullRank*`, `RSCurveListSize*`, `Frank*`, `GMMDS*`, `K4*`,
  `BatchingConsistency*`. Hensel/Faà-di-Bruno bijections + moment-method list-size bounds.
- **`Lemma5_8EagerBirthdayResidual`**: tier-(b) **REFUTED as stated** (B1 defect, committed
  countermodel). The faithful `EPaper`-repair `Lemma5_8EagerPaperResidual` IS proven (this campaign).
- **STIR / composition / query-round seams**: `stir*RbrSoundnessResidual`, `appendRbr*Phase2*`,
  `appendToReductionResidual`, `appendRunRightResidual`, `queryRound*Residual`, `r1csResidual`,
  `LogupSoundness*Residual`, `duplexSpongeFiatShamirSalted_runCollapseResidual`. Reduction-level
  composition obligations; several are proven at point-mass via the state-collapse keystones.

- `BatchingConsistencyResidual`
- `BoundaryCardStrictInteriorResidual`
- `D2fOuterImplSharedBudgetResidual`
- `D2sQueryStepGSpecBudgetResidual`
- `FrankOrientationResidual`
- `GKL24FirstMomentResidual`
- `GKL24MaxCorrStrictWitnessCoverResidual`
- `GKL24MaxDomainWitnessCoverResidual`
- `GMMDSResidual`
- `Hyb01StepResidual`
- `Hyb12StepResidual`
- `Hyb23StepResidual`
- `Hyb34StepResidual`
- `K4ComponentResidual`
- `KeyLemmaEagerResidual`
- `KeyLemmaEagerSaltedResidual`
- `KeyLemmaResidual`
- `Lemma5_12HonestResidual`
- `Lemma5_14HonestResidual`
- `Lemma5_16HonestResidual`
- `Lemma5_8EagerBirthdayResidual`
- `LogupSoundnessFullResidual`
- `LogupSoundnessUncondResidual`
- `OuterCompletenessRunFactsResidual`
- `RIMFullRankFailureProbResidual`
- `RSCurveListSizeResidual`
- `RestrictedFaaDiBrunoMatchResidual`
- `SimulatedProverChallengeBudgetResidual`
- `SimulatedProverSharedBudgetResidual`
- `StrictCanonicalCoeffPolysResidual`
- `appendRbrKnowledgeSoundnessPerRoundResidual`
- `appendRbrKnowledgeSoundnessPhase2Residual`
- `appendRbrSoundnessPhase2Residual`
- `appendRunRightResidual`
- `appendToReductionResidual`
- `duplexSpongeFiatShamirSalted_runCollapseResidual`
- `queryRoundChainDeliveryResidual`
- `r1csResidual`
- `stirCheckingRbrSoundnessResidual`
- `stirMultiRoundRbrSoundnessResidual`

## DISCHARGED (unconditional)

- `AppendCompletenessResidual`
- `AppendSoundnessResidual`
- `DeepHoleProbResidual`
- `Hyb4ChallengeEntryResidual`
- `Lemma5_8EagerPaperResidual`
- `LogupCompletenessBrickResidual`
- `LogupSoundnessBrickResidual`
- `OuterCompletenessRunResidual`
- `OuterSoundnessResidual`
- `SubPhaseCompletenessResidual`
- `SubPhaseSoundnessResidual`
- `SumcheckCompletenessResidual`
- `SumcheckSoundnessResidual`
- `appendCompletenessResidual`
- `appendPerfectCompletenessResidual`
- `appendSoundnessResidual`
- `composedCompletenessResidual`
- `composedCompletenessWithClaimResidual`
- `composedPIOPResidual`
- `composedPIOPWithClaimResidual`
- `composedRbrKnowledgeSoundnessResidual`
- `composedRbrKnowledgeSoundnessWithClaimResidual`
- `duplexSpongeFiatShamir_runCollapseResidual`
- `fiatShamir_hvzkTransferResidual`
- `fiatShamir_knowledgeSoundnessTransferResidual`
- `fiatShamir_runCollapseResidual`
- `fiatShamir_soundnessTransferResidual`
- `fiatShamir_statisticalHVZKTransferResidual`
- `finalCheckWithClaimValueRelResidual`
- `finalFoldRoundPerfectCompletenessResidual`
- `firstSumcheckResidual`
- `foldRoundPerfectCompletenessResidual`
- `r1csMleEncodingResidual`
- `reductionAppendCompletenessResidual`
- `reductionAppendPerfectCompletenessResidual`
- `secondSumcheckResidual`
- `secondSumcheckTerminalEndpointResidual`

## REDUCED (conditional on a named hypothesis)

- `BoundaryCardLatticeResidual`
- `BoundaryCardLatticeThresholdResidual`
- `BoundaryCardResidual`
- `BoundaryProbabilityResidual`
- `CurveCommonAgreementResidual`
- `FaaDiBrunoSuccSumZeroResidual`
- `GKL24FirstMomentWitnessCoverResidual`
- `GKL24MaxCorrWitnessCoverHypothesis`
- `GKL24PetalWitnessCoverHypothesis`
- `K4GradedFactorCellResidual`
- `OuterCompletenessResidual`
- `StrictCoeffPolysExcResidual`
- `StrictCoeffPolysLargeResidual`
- `StrictCoeffPolysResidual`
- `StrictCoeffPolysShareResidual`
- `SymbolicFullRankResidual`
- `appendKnowledgeSoundnessResidual`
- `appendRbrKnowledgeSoundnessResidual`
- `appendRbrSoundnessResidual`
- `composedCompletenessWithClaimSecondSumcheckEvalResidual`
- `composedCompletenessWithClaimValueRelResidual`
- `composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalResidual`
- `composedRbrKnowledgeSoundnessWithClaimValueRelResidual`
- `oracleReductionToReductionResidual`
- `randomLinearLambdaLowerFirstMomentResidual`
