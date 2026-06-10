# ArkLib proof-debt ledger — CLASSIFIED (triage wf_0b77f269-416, 2026-06-10)

Source code is clean of `sorry`/`admit`/`axiom`/`native_decide` (all grep hits are docstring
text; verified by `scripts/audit_ledger.py`). All remaining debt is named-Prop shaped.
Raw classification data: `audit/triage-2026-06-10.json`.

## Session updates (2026-06-10, orchestrator inline work — between triage and wave 1 relaunch)

- **[RESOLVED] epsMCAgsPrizeUniformConjecture** — proven as stated (`epsMCAgsPrizeUniformConjecture_holds_as_stated`, `GrandChallenge141UniformVacuity.lean`, axiom-clean, commit 8c0f1d42a); docstrings de-laundered (ba2a433fa). Open content relocated honestly to `epsMCAgsPrizeUniversalConjecture`/`UniversalGSListMassBound`.
- **[RESOLVED] red-on-main: GrandChallenge141PrizeMath.lean** — 3 call sites repaired after the MCAGS 8-arg→2-arg refactor; 8-arg theorem renamed `epsMCAgs_prizeBound_perInput_holds` (name clash with UniformResolved removed); LowOutput green (8c0f1d42a).
- **[RESOLVED] Spartan "bit-rot" was phantom** — `FirstChallengeComplete`, `ComposedCompletenessFinal` (apex `composedCompletenessResidual_proven` axiom-clean, 0 sorryAx), `ComposedCompletenessWithClaimFinal`, `ComposedCompletenessTwoLeaves` all verified green after clean olean builds. Parallel session additionally discharged `hSeamZero` and verified `composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves`. Spartan remaining: 6 short-phase rbr-KS leaves + of_leaves instantiation + D1 pair.
- **[RESOLVED] doc de-laundering** (ba2a433fa): `epsMCAgs_prizeBound_conjecture_of_uniform` (consumes a refuted hypothesis — now says so), `whirVectorIOP_rbrKnowledgeSoundness_dummy` (not a #302 resolution — trivial-budget demo).
- **[RESOLVED earlier] 3 false-axiom HonestAxioms.lean files deleted** — project has zero axiom declarations.
- Wave 1 (10 agents) relaunches 6:48am after the subagent session-limit reset.

**Live count (regenerated 06:00 6/10):** residual-named surfaces 449 → 435 (−14: inline deletions, #328 vacuity-trap class removal, PrizeMath renames, wave-tagged landings incl. 684f50ec2 GenMutualCorrParams instance). Invariants re-verified: sorry=0, native_decide=0, axiom=0.

**Totals (families):** proven 118 · provable 73 · open-research 20 · dead 20

- **proven** — the named residual is discharged in-tree (discharger cited; existence grep-verified)
- **provable** — open, with a concrete route (effort S/M/L; papers listed in PAPERS_NEEDED.md)
- **open-research** — genuinely open math (#232/#141 prize class); consumers stay conditional
- **dead** — unconsumed/refuted-as-stated; deletion or documented-false-surface candidates


## ArkLib/Data/CodingTheory/** — all 207 residual-named decls listed in AUDIT_LEDGER.md lines 29-235 (P

### [OPEN-RESEARCH] mcaConjecture + mcaConjectureBound (ABF26 §4.5)
- loc: `ProximityGap/GrandChallenges.lean:516,489`
- #232/#141 maintainer keep-open prize surface. mcaConjectureBound is a plain RHS definition (no debt). mcaConjecture is the genuinely open ABF26 §4.5 draft conjecture, honestly documented ('keep as a named hypothesis'); moreover EXPECTED FALSE: in-tree conditional refutation not_mcaConjecture_of_cs25BreakdownBelowBound awaits only the CS25 port. Cannot be closed; end-state = named Prop + conditional consumers (already the case).
- papers: ABF26 §4.5; CS25
### [OPEN-RESEARCH] UniformPolyListSizeConjecture
- loc: `ProximityGap/Issue141Kernels.lean:51`
- Field-independent poly list-size at capacity radius 1-rho-eta = the #141/#232 prize core. GENUINELY OPEN as stated (no in-tree refutation), though prime-field super-poly counterexamples (KK25 / arXiv 2604.09724 direction, in-tree UpToCapacityFalse* analogues) make the small-eta regime expected false. Keep named Prop; consumer epsMCAgs_prizeBound_of_uniform_listSize is conditional (and itself a pass-through, see findings).
- papers: #141/#232; KK25
### [OPEN-RESEARCH] epsMCAgsPrizeUniversalConjecture + UniversalGSListMassBound (+ epsMCA_le_of_universalGSConjecture, _of_UniversalGSListMassBound)
- loc: `GrandChallenge141UniformResolved.lean:126,150,205 (UniversalGSListMassBound ~:184)`
- THE genuine #141/#232 surface: constants quantified before the field, faithful-L existential (explicitly designed so fixed-field inflation and the non-faithful refutation both fail). The two bridge theorems are proven (verified bodies, via proven epsMCAgs_le_listSize_div_of_pivotCovering). Cannot be closed — beyond-UDR field-universal GS list-mass bound is the prize. End-state already honest: named Props + proven reductions.
- papers: #141/#232; ABF26 GC1
### [PROVABLE (L)] BoundaryCardLatticeThresholdResidual + boundaryCardLatticeThresholdResidual_of_extraction
- loc: `BoundaryLatticeThresholdLeaf.lean:196,206`
- The O76-corrected lattice leaf (Pr > k·(n+1)/|F| replaces bare 0<card). Reduces (proven) to LatticeCoeffPolyExtraction = BCIKS20 §5 coefficient-polynomial extraction at the exact lattice endpoint. Same open core as StrictCoeffPolysResidual.
- papers: BCIKS20 §5-6
### [PROVABLE (M)] diffStackMCAResidualBelowUDR + _of_epsCA_ge
- loc: `ProximityGap/Errors.lean:1597,1632`
- Brick _of_epsCA_ge PROVEN (verified). Residual = ABF26 L4.6 hard direction; abstract-code form documented FALSE (kernel-refuted double-coverage), RS form discharges via the named Prop GSWitnessLowerBound (ToMathlib/L46GSLowerBound.lean) with RS witness machinery in ToMathlib/L46DiffStackRS.lean. Remaining input = the BCIKS20-style GS witness existence for RS.
- papers: ABF26 §4.6; BCIKS20/ACFY25/Hab25
### [PROVABLE (L)] CS25BreakdownBelowConjectureBound + not_mcaConjecture_of_cs25BreakdownBelowBound
- loc: `ProximityGap/MCAConjectureRefutation.lean:47,62`
- Refutation implication PROVEN (verified body, via epsCA_le_epsMCA). The Prop itself = port CS25's epsCA=1 near-capacity breakdown band + check it sits below the polynomial bound at large field; in-tree reduction cs25BreakdownBelowBound_of_breakdownFamily already proven; external input = rs_epsCA_breakdown_cs25 (named Prop, CapacityBounds.lean:666, honest external debt per ProximityGap/ExternalDebt.lean).
- papers: CS25 (ECCC); ABF26 §4.5
### [PROVABLE (S)] epsMCAgsPrizeUniformConjecture (per-domain 'uniform prize')
- loc: `ProximityGap/GrandChallenge141PrizeMath.lean:173`
- VACUITY: statement is identical in content to MCAGS.epsMCAgs_prizeBound_conjecture domain m, which is PROVEN trivially true in GrandChallenge141UniformResolved.lean:78 (constants (0,0,n) with (15/16)^n <= 1/q — fixed-field inflation; eta <= 15/16 from prizeRates >= 1/16). Its docstring still claims 'the honest open GS-exposed prize... deliberately unproved' — WRONG/superseded. Route: copy the UniformResolved proof, then re-point or delete the dependent pyramid.
### [PROVABLE (L)] Hab25JohnsonResiduals structure + ofAlgebraicData/toAlgebraicData + disagree_card_le + 4 NumericBridge packagings
- loc: `ProximityGap/Hab25Johnson.lean:329-392; Hab25JohnsonNumericBridge.lean:122-186`
- Converters and disagree_card_le are proven bricks (claim1_theorem2_integer verified to exist and be consumed). The bundle fields (hcover S4, hImprove S6->S8, hNumeric S11) are the genuine Hab25 §3 inputs not yet constructed for real instances — provable from the paper; in-tree frontier per prior audits = hImprove weld + Z-degree budget + S11.
- papers: Hab25 (ECCC 2025/169) §3
### [PROVABLE (L)] StrictCoeffPolysResidual + StrictCanonicalCoeffPolysResidual + CurveCommonAgreementResidual + RSCurveListSizeResidual (the §5 strict-Johnson open core)
- loc: `BCIKS20/Curves.lean:2505,2528; Curves/CoeffExtractionResidual.lean:30; Curves/ListSizeResidual.lean:45`
- The single research-grade input for the strict-Johnson RS proximity gap: BCIKS20 §5 trivariate Guruswami-Sudan list-size/coefficient-polynomial extraction. Consumers (correlatedAgreement_affine_curves and wrappers, RS_jointAgreement_of_curveListSizeResidual, strictCoeffPolysResidual_of_commonAgreement) all proven conditionals. Live route = Claim57 descended pipeline; substantial but known paper math.
- papers: BCIKS20 §5 (Thm 1.5, Claims 5.4-5.9)
### [PROVABLE (L)] Claim57Residuals / Claim57ResidualsDescended classes + 6 constructors (ofGraphExtractionHypotheses, ofInTree, ofInTree2, Descended.ofInTree, ofDescended, ofDescendedInTree)
- loc: `BCIKS20/ListDecoding/Agreement.lean:1815,1843; Claim57FieldDischarge.lean:449,494; DescendedRset.lean:410,538,682,714`
- Assumption-carrying typeclasses, NO unconditional instance (only letI from supplied hypotheses — verified). Constructors are proven surface-shrinking bricks (ofInTree2 discharges hx0 outright). Remaining genuine inputs: hsepPt (separability over F[Z] base), hlarge (field/largeness budget), hfactor (documented 'not provable outright'); descended route eliminates hfactor but Claim57Residuals.ofDescended is hcoincide-gated (pg_RsetDescended = pg_Rset, FALSE in the inseparable case). Descent localizes Claim 5.7 to two tractable residuals.
- papers: BCIKS20 §5 Claim 5.7
### [PROVABLE (L)] randomLinearLambdaLowerFirstMomentResidual + _of_exists_event + exists_code_of_
- loc: `ListDecoding/Bounds/RandomAndReedSolomon.lean:142,200,224`
- GLMRSW22 T3.11 first-moment positivity Prop; the two bridges are proven bricks (positivity from one good matrix; code extraction). Closing needs random-linear-code probability infra + the paper's lower-bound argument — honest external debt per ExternalDebt.lean.
- papers: GLMRSW22 (ABF26 T3.11)
### [PROVABLE (L)] GKL24 first-moment family: 4 residual defs (FirstMoment, WitnessCover, MaxCorr(Strict)WitnessCover, PetalWitnessCover, MaxDomainWitnessCover) + 3 inTree instantiations + 6 cover-conversion theorems
- loc: `Connections/GKL24FirstMoment.lean:1045-1503; Connections/GKL24PetalWitnessCover.lean:56,84`
- Parameterized Props: PROVEN in-tree at relaxed parameters (B_T=|F|^n, b=n and b=max 1 (2δn): _inTree_card, _inTree_two_delta_card, _inTree_delta_add_one_card — verified) and all cover-form conversions proven (incl. gkl24PetalWitnessCoverResidual_of_maxDomainWitnessCover, verified). Open at the sharp GCXK25 parameters B_T=L², b=δ_list·n — the genuine GKL24 Lemma-1/maximal-agree-domain charging argument.
- papers: GKL24; GCXK25 T5.1
### [DEAD] BoundaryCardResidual + BoundaryProbabilityResidual (bare boundary nonemptiness Props)
- loc: `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:2568,2582`
- REFUTED as stated, in-tree and axiom-clean: not_boundaryCardResidual / not_boundaryProbabilityResidual (BoundaryCardResidualRefutation.lean:246,274), not_boundaryCardResidual_affineLine (AffineLineRefutation.lean:118), not_boundaryCardResidual_nonSquareEndpoint (StrictInteriorRefutation.lean:311). Even the formalized Thm-1.5 conclusion is refuted at the closed boundary (not_delta_epsilon_correlatedAgreementCurves_boundary). Keep only as documented-false adapter surfaces; all consumers (correlatedAgreement_affine_curves_of_boundaryCardResidual etc.) are explicitly conditional.
### [DEAD] BoundaryCardLatticeResidual, BoundaryCardStrictInteriorResidual, BoundaryCardQuantizationResiduals, BoundaryCardLatticeData/SubResiduals (lattice-split surfaces)
- loc: `BoundaryCardResidual.lean:203,267,409; BoundaryCardLatticeSlice.lean:131`
- All bare nonemptiness-style leaves refuted in-tree (not_boundaryCardLatticeResidual:252, not_boundaryCardQuantizationResiduals:267, not_boundaryCardStrictInteriorResidual:299, not_boundaryCardLatticeData). Docstrings already say 'false in general; remains only as explicit assumption surface for older adapters'. Superseded by the threshold-corrected leaf below.
### [DEAD] uniformEpsMCAgsPrizeBoundConjecture + not_uniformEpsMCAgsPrizeBoundConjecture
- loc: `ProximityGap/MCAGS.lean:564; MCAGSPrizeRefutation.lean:102`
- The forall-L fully-uniform form is UNCONDITIONALLY REFUTED in-tree (axiom-clean; non-faithful L={w0} drives epsMCAgs=1 over ZMod p, p>2^(c2+c3)) — the formalization dropped the FAITHFUL clause. Refutation theorem itself is proven (verified). Keep def only as the documented-false statement; bridge epsMCAgs_prizeBound_conjecture_of_uniform (MCAGS.lean:582) now consumes a refuted Prop and should say so. Duplicate refutation kept at ArkLib/MCAGSRefutationCore_keep.lean:101.
### [DEAD] ~74-theorem *_of_uniformConjecture pyramid (GrandChallenge141PrizeMath.lean x27 + GrandChallenge141PrizeMathLowOutput.lean x10: adapters, mass-bound iff, witness/lattice/threshold/bracket packagings)
- loc: `GrandChallenge141PrizeMath.lean:191-1419; GrandChallenge141PrizeMathLowOutput.lean:36-419`
- All proven as stated, but conditional on the trivially-true per-domain Prop above, so they carry zero prize content; zero consumers outside the two files (verified by grep). Deletion candidates or mechanical re-pointing at epsMCAgsPrizeUniversalConjecture.
### [DEAD] 3 stale ledger entries at ListDecoding/Bounds.lean:1461/1519/1543
- loc: `ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean (now 146 lines)`
- LEDGER STALENESS, not code debt: Bounds.lean was split into Bounds/ submodules; these decls now exist only in Bounds/RandomAndReedSolomon.lean (previous item). Regenerate AUDIT_LEDGER.md.
### [PROVEN] 7 BoundaryCard refutation theorems (not_boundaryCard*, not_boundaryProbability*, both leaves of quantization split)
- loc: `BoundaryCardResidualRefutation.lean:246-274; BoundaryCardStrictInteriorRefutation.lean:299,311; BoundaryCardResidualAffineLineRefutation.lean:118`
- Explicit small-field (ZMod 5 / deg·n square and non-square) witnesses; files carry #print axioms blocks; verified theorem bodies read.
### [PROVEN] ~24 BoundaryCard converter/quantization bricks (boundaryCardResidual_of_not_lattice, *_zero, ofStrictInterior_zero, lattice/strictInterior splits, toBoundaryCardResidual(_isSquare), of/not_isSquare_deg_mul_card pairs, boundaryCardLatticeResidual_of_subResiduals, boundaryProbabilityResidual_of_subResiduals, latticeResidual_target_is_boundary_good_set)
- loc: `BoundaryCardResidual.lean:232-1024; BoundaryCardLatticeSlice.lean:157-223`
- Pure quantization/floor-transport and repackaging bricks ABOUT the (refuted) Props; verified proof bodies; subResiduals_iff_latticeData is an intentional Iff.rfl identity certificate.
### [PROVEN] GK16Lemma12HardResidual + _reduces_hard + gk16Lemma12HardResidual_holds
- loc: `ProximityGap/GK16Lemma12.lean:400,413,440`
- DISCHARGED: gk16Lemma12HardResidual_holds proves the Prop via ToMathlib/GK16Finish.lean exists_distinctDegree_recombination (Gaussian elimination on degrees, verified to exist); apex foldedWronskian_ne_zero_of_linearIndependent is unconditional.
### [PROVEN] 10 GrandChallenges positive-direction links (nonempty/exists_mcaLowerWitness_of_(ignoredSource_/ignored_)mcaConjecture + allRates/prize variants)
- loc: `GrandChallenges.lean:536-687`
- Verified conditional bricks consuming the open mcaConjecture Prop; quantifier plumbing only, honestly documented as adapters.
### [PROVEN] 24 GrandChallengesLattice conditional theorems (GrandChallengesLatticePrizeSpec.lean x16, Lattice/Witnesses.lean x7, Lattice/Prize.lean x1, all *_of_(ignoredSource_)mcaConjecture)
- loc: `GrandChallengesLatticePrizeSpec.lean:722-1297; GrandChallengesLattice/Witnesses.lean:400-501; GrandChallengesLattice/Prize.lean:227`
- Proven conditional bracket/threshold/witness packaging over mcaConjecture. Self-contained cone (no consumers outside these 4 files); harmless but prunable since mcaConjecture is expected false (CS25). Given they are honest conditionals, classify proven not dead.
### [PROVEN] GrandChallenge141Progress quartet (epsMCA_le_mcaConjectureBound_of_one_le_bound; mcaConjecture iff/intro/elim AbstractRSMcaPolyBound)
- loc: `GrandChallenge141Progress.lean:78,116,121,126`
- Unconditional bound>=1 special case proven (verified); the iff/intro/elim are intentional definitional pass-throughs (Iff.rfl / := h) documented as surface-conversion rules — listed under pass-throughs.
### [PROVEN] 11 strict-coeff producer/reduction bricks (strictCoeffPolysResidual_of_strictCanonical..., of_rawGSCargo, of_localSeriesDatumOn, of_commonAgreement, StrictCoeffLargeReduction x5 incl. iff_large, correlatedAgreement_affine_curves_of_largeResidual)
- loc: `BCIKS20/Curves.lean:2554; LocalSeriesProducer.lean:483; StrictCoeffProducer.lean:423; CoeffExtractionResidual.lean:59; StrictCoeffLargeReduction.lean:96-150`
- Verified proof bodies: Lagrange small-sector unconditional discharge, canonical-family transport, conditional producers from GS cargo/local-series data. strictCoeffPolysResidualLarge_of_residual is a trivial converse (documented).
### [PROVEN] 6 CoeffExtractionVacuous discharges (curveCommonAgreementResidual/strictCoeffPolysResidual _of_one_le_mul/_of_card_le/_of_card_le_e7)
- loc: `BCIKS20/Curves/CoeffExtractionVacuous.lean:42-183`
- Honest, explicitly-labeled vacuous-regime discharges (probability hypothesis unsatisfiable when q <= k·n or q <= k·deg²·10^7). Real-regime content stays open in the §5 core above; not laundering.
### [PROVEN] Hensel weight trio: βHenselSuccTermWeightResidual + Structured variant + of_structured + βHenselSuccTermStructuredWeightResidual_holds
- loc: `BCIKS20/HenselNumerator.lean:1598,1679,1699,2690`
- The per-term wall is DISCHARGED (_holds verified at 2690, given the structured invariant, which AlphaWeight.lean:620-748 supplies from alphaWeight/divWeight). Remaining genuinely-open content in this cone is the P1 weight-1 quotient bound (#138)/gamma-is-a-root core, tracked separately, not these ledger decls.
- papers: BCIKS20 App A
### [PROVEN] FaaDiBrunoSuccSumZeroResidual + RestrictedFaaDiBrunoMatchResidual + 11 P2 bricks/bridges (Assembly, RootBridge, Vanish, MonicWfreeGlobal/RangeConsumers, MonicConsequences)
- loc: `HenselNumerator.lean:2454; P2MatchProof.lean:30; P2Assembly.lean:460,538; P2RootBridge.lean:54,125; P2Vanish.lean:187,196; P2MonicWfreeGlobal.lean:127; P2MonicWfreeRangeConsumers.lean:47; P2MonicConsequences.lean:45`
- Honest split, fully resolved: PROVEN for monic H (the BCIKS20 WLOG case) via restrictedFaaDiBrunoMatch_of_monic (P2MatchMonic.lean, verified) -> P2_closed_of_leadingCoeff_one / faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one; REFUTED for the concrete non-monic witness (next item). RestrictedFaaDiBrunoMatchResidual is an alias def explicitly de-laundering a former fabricated axiom.
- papers: BCIKS20 App A.4
### [PROVEN] 4 P2 order-zero refutations (faaDiBrunoSuccSumZeroResidual_false + 3 _false_of_constant_of_* variants)
- loc: `P2OrderZeroRefutationWitness.lean:168; P2OrderZeroRefutation.lean:309,321,335`
- Concrete-witness refutations of the non-monic case (verified body of _false). Together with the monic discharge these close the residual's status completely.
### [PROVEN] MCAGSPrizeVacuity + GrandChallenge141UniformResolved per-input/fixed-field theorems (epsMCAgs_prizeBound_conjecture_holds x2, epsMCA(gs)_le_one)
- loc: `MCAGSPrizeVacuity.lean; GrandChallenge141PrizeMath.lean:~135; GrandChallenge141UniformResolved.lean:78`
- Honest anti-vacuity/vacuity-documentation theorems: empty-L form vacuous, per-input form trivially true, fixed-field uniform form trivially true. These are the key facts that demote the PrizeMath pyramid (see laundering findings).

**Pass-throughs found:**
- mcaConjecture_iff_abstractRSMcaPolyBound — GrandChallenge141Progress.lean:116 (Iff.rfl; documented intentional surface equivalence)
- mcaConjecture_of_abstractRSMcaPolyBound — GrandChallenge141Progress.lean:121 (:= h)
- abstractRSMcaPolyBound_of_mcaConjecture — GrandChallenge141Progress.lean:126 (:= h)
- epsMCAgs_prizeBound_of_uniform_listSize — MCAGS.lean:~552 (body = h_reduction h_listSize; assumes its own reduction — flagged in laundering findings)
- subResiduals_iff_latticeData — BoundaryCardLatticeSlice.lean:157 (Iff.rfl; documented definitional-identity certificate)
- latticeResidual_target_is_boundary_good_set — BoundaryCardLatticeSlice.lean:223 (rfl; documented audit-narrative sanity)
- strictCoeffPolysResidualLarge_of_residual — BCIKS20/StrictCoeffLargeReduction.lean:133 (trivial weakening, hypothesis dropped; documented 'trivial converse')
- RestrictedFaaDiBrunoMatchResidual — BCIKS20/P2MatchProof.lean:30 (alias def := RestrictedFaaDiBrunoMatch; intentional de-laundering of a former fabricated axiom)

**Laundering/vacuity findings:** THREE positive findings, no deletion-laundering. (1) VACUITY MISLABELED AS OPEN PRIZE: epsMCAgsPrizeUniformConjecture (GrandChallenge141PrizeMath.lean:173) docstring claims 'The honest open GS-exposed prize... deliberately unproved; downstream must take it as explicit hypothesis'. But its statement is content-identical to MCAGS.epsMCAgs_prizeBound_conjecture domain m, which GrandChallenge141UniformResolved.lean:78 PROVES trivially true for every fixed field (constants (0,0,n), (15/16)^n <= 1/q inflation, since prizeRates >= 1/16 forces eta <= 15/16). Hence the entire ~74-theorem *_of_uniformConjecture pyramid in PrizeMath + PrizeMathLowOutput conditions on a trivially-true Prop and carries no prize content (and has zero external consumers). The genuine open surface is epsMCAgsPrizeUniversalConjecture / UniversalGSListMassBound (UniformResolved.lean), which fixes both failure modes (constants before the field; faithful-L existential). Fix: correct the docstring, prove the Prop by copying the UniformResolved proof or delete the pyramid. (2) PASS-THROUGH POSING AS A REDUCTION: epsMCAgs_prizeBound_of_uniform_listSize (MCAGS.lean:~552) — docstring says it 'proves that the open prize conjecture follows... by providing the reduction explicitly', but the reduction itself is hypothesis h_reduction and the body is `h_reduction h_listSize` (bare modus ponens); it wires nothing. (3) REFUTED PROP STILL BRIDGED: uniformEpsMCAgsPrizeBoundConjecture is unconditionally refuted (MCAGSPrizeRefutation.lean:102) yet MCAGS.lean:582 epsMCAgs_prizeBound_conjecture_of_uniform still offers it as a hypothesis route without a pointer to the refutation. Deletion-laundering spot-check: all 9 docstring-referenced discharging decls verified to exist by grep (exists_distinctDegree_recombination, claim1_theorem2_integer, restrictedFaaDiBrunoMatch_of_monic, epsMCAgs_le_listSize_div_of_pivotCovering, L46GS.floorCount_le_epsCA_of_gsWitness, goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary, jointAgreement_of_latticeThreshold_of_coeffPolys, claim57Residuals_of_gsInterpolant, correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary) — none missing. Ledger staleness: 3 entries point at ListDecoding/Bounds.lean:1461/1519/1543, which no longer exist after the Bounds/ split (decls live in Bounds/RandomAndReedSolomon.lean); regenerate scripts/audit_ledger.py output.

## ArkLib/ToMathlib/** — all 81 residual-named declarations listed in AUDIT_LEDGER.md section ToMathlib

### [PROVABLE (L)] randomRSListDecodingFirstMomentResidual (def)
- loc: `ArkLib/ToMathlib/AGL24RandomRSProof.lean:78`
- Genuinely open named input: Pr[bad-domain] <= failure for uniformly sampled size-n RS domains. No _holds, no consumers outside file (only the proven in-file front-door reductions random_rs_list_decoding_of_first_moment_residual / _of_prob_bound). Route: formalize the AGL24 first-moment counting argument over uniformSizeSubsetOfLe; mirror the landed GLMRSW22 random-linear endpoint in ListDecoding/Bounds.lean.
- papers: AGL24 Thm 1.1 (ABF26 T3.6), issue #95
### [PROVABLE (M)] foldRoundPerfectCompletenessResidual + finalFoldRoundPerfectCompletenessResidual (defs)
- loc: `ArkLib/ToMathlib/FriComplete.lean:106,131`
- Open named per-round FRI perfect-completeness Props, consumed as hypotheses by Fri/Spec/Completeness.lean (conditional composition). Route: mirror the PROVEN Binius sibling foldOracleReduction_perfectCompleteness (~150-line 2-message monadic unrolling); algebraic core RoundConsistency.generalised_round_consistency_completeness is already proven; use unroll_2_message_reduction_perfectCompleteness keystone (OracleReduction/Completeness.lean:551) with hInit : NeverFail.
- papers: issue #117; FRI (BBHR18) round consistency
### [PROVABLE (M)] MonicHighYResidual (structure)
- loc: `ArkLib/ToMathlib/GSGradedBundle.lean:283`
- Per-bundle named GS-factor input: (i) H monic in Y, (ii) 2 <= deg_Y R. DISCHARGED at the witness bundle (FaithfulFrontierWitness.lean:121 theorem residualw — grep-verified) and the hmonic half at unit-leadingCoeff endpoints (BranchCollapse.lean:133 monic_bundle_of_isUnit_leadingCoeff). General discharge for arbitrary normalizedFactors bundles is the A.4 monicization/clearDenomY wall; hd2 is intentionally per-bundle (the deg_Y<=1 affine branch is handled separately). Honest end-state: keep as per-bundle data field; proven consumer section5DataOffcentreFin_of_gradedBundle_residual pins it as exactly the remaining gap.
- papers: BCIKS20 SS5 / Hab25 A.4
### [PROVABLE (L)] PerZResidual (structure)
- loc: `ArkLib/ToMathlib/GSLineInputSupply.lean:216`
- Per-word named input: six per-z fields (non-collapse, degree, two GS-Johnson proximities, order-0 agreement, separability) about the canonical integer representative. Producers gsLineInput_of_chain/_of_johnson proven; no discharger in tree. Route: BCIKS20 SS5 / Hab25 S10 per-z geometry for the canonical GS interpolant in the Johnson regime; separability interacts with the documented inseparable/descended-Claim5.7 frontier.
- papers: BCIKS20 SS5, Hab25 S10
### [PROVABLE (M)] composedCompletenessWithClaimValueRelResidual:1117 + composedCompletenessWithClaimSecondSumcheckEvalResidual:1128 (defs)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1117,1128`
- Equivalent pair (proven iff :1141) — completeness into the SEMANTIC target relation (carried target = second-sum-check endpoint). Not discharged: the current prependClaim/prependTarget adapter emits target 0 (the documented D1 design gap), so the honest composition must thread the genuine RLC target value. Route: build the value-carrying claim adapter (variant of prependRLCTarget emitting finalExpectedClaimValue), reprove its 0-round perfect completeness (pattern: prependSlot PCs, Spartan.Spec.Bricks), then reuse composedCompletenessResidual_proven_114c assembly.
- papers: issue #114 (D1)
### [PROVABLE (L)] composedRbrKnowledgeSoundnessResidual (def)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1234`
- Reduced (not closed): Bricks.composedRbrKnowledgeSoundnessResidual_of_leaves (ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:626, [Subsingleton sigma]) folds the seven append seams at Rc := composedPIOP_Rc down to: 8 per-phase rbr-KS leaves (standard: RandomQuery / Sumcheck.Spec per-round 2/|R| / CheckClaim — known proofs exist per-leaf), 7 verifier-determinism witnesses (rfl-shaped), and 2 challenge-seam hSeamZero residuals. Remaining work is known-math engineering, no new mathematics.
- papers: issue #114; Spartan (Setty20) + sum-check rbr
### [PROVABLE (L)] composedRbrKnowledgeSoundnessWithClaim{Residual:1254, ValueRelResidual:1267, SecondSumcheckEvalResidual:1280} (defs)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1254-1280`
- Target-carrying rbr variants; only conditional surfaces exist (the :1549 pass-through and its ProofSystem delegation spartan_rbr_knowledge_soundness_with_claim). Route: discharge :1234 via the leaves fold, then append the claim adapter seam (0-round, deterministic verifier — same keystone family as the completeness WithClaim discharge); ValueRel/Eval variants additionally need the D1 target-emitting adapter.
- papers: issue #114
### [PROVEN] BoundaryDischarge conditional bricks (10 thms: boundaryCardResidual_of_boundary_cards_and_coeffPolys:285, boundaryCardLatticeResidual_of_boundary_cards_and_coeffPolys:314, boundaryCardLatticeResidual_of_lattice_data:343, BoundaryCardQuantizationData.toQuantizationResiduals:448 / .toBoundaryCardResidual:459 / .toBoundaryProbabilityResidual:468, boundaryCardResidual_of_lattice_data:497, boundaryProbabilityResidual_of_lattice_data:518, boundaryCardResidual_of_lattice_data_isSquare:568, boundaryProbabilityResidual_of_lattice_data_isSquare:585)
- loc: `ArkLib/ToMathlib/BoundaryDischarge.lean:285-599`
- All are real axiom-clean reduction bricks (assembly bridge boundary_jointAgreement_of_cards_and_coeffPolys + lattice/isSquare adapters), #print axioms audited in-file. CAVEAT: the concluded Props (BoundaryCardResidual / BoundaryCardLatticeResidual) are REFUTED at concrete instances (not_boundaryCardResidual, BoundaryCardResidualRefutation.lean:246/252; affine-line and non-square-endpoint refutations), so the hypothesis bundles (BoundaryCardLatticeData etc., Data/CodingTheory scope) are unsatisfiable there; honest boundary surface has moved to the BoundaryHalfState johnsonClosed leaves. Keep as documented adapters; consumers are clearly conditional.
### [PROVEN] boundaryCardResidual_zero + boundaryProbabilityResidual_zero
- loc: `ArkLib/ToMathlib/BoundaryDischarge.lean:628,638`
- Unconditional: residuals are vacuous at k=0 (first argument 0<k). Honest, docstring states vacuity explicitly; purpose is removing dead hypotheses from degenerate callers.
### [PROVEN] correlatedAgreementCurves_boundary_of_largeResidual_cellMin
- loc: `ArkLib/ToMathlib/BoundaryHalfState.lean:183`
- Real composite (O70 front door + O79 monotone-eps floor-cell transport + O76 floor transport), conditional on the named open leaf StrictCoeffPolysResidualLarge (BCIKS20/StrictCoeffLargeReduction.lean:96) at the cell radius. Note: BoundaryHalfState.lean is imported nowhere — capstone correlatedAgreementCurves_johnsonClosed_of_leaves in same file is the honest Johnson-endpoint dichotomy; consider wiring or flagging as standalone.
### [PROVEN] CS25 deep-hole chain (4: DeepHoleProbResidual def CS25DeepHoleFinish.lean:262, hDeepHole_of_probResidual :278, deepHoleProbResidual_of_jointFar CS25DeepHoleFinish2.lean:259, deepHoleProbResidual_holds CS25JointFar.lean:203)
- loc: `ArkLib/ToMathlib/CS25DeepHoleFinish.lean:262,278; CS25DeepHoleFinish2.lean:259; CS25JointFar.lean:203`
- FULLY DISCHARGED chain (issue #22 closed): deepHoleProbResidual_holds EXISTS (grep-verified) and instantiates DeepHoleProbResidual with only the arithmetic rate condition k < n - floor(delta*n); composes deepHoleProbResidual_of_jointFar with the minimum-distance proof deepHoleJointFar_holds (CS25JointFar.lean:93). Apex rs_epsCA_implies_lambda_extended_cs25_complete(_prop) consumes it end-to-end; #print axioms audited.
### [PROVEN] claim57Residuals_of_johnson + claim57Residuals_of_natCeil_johnson
- loc: `ArkLib/ToMathlib/Claim57Supply.lean:169,205`
- Proven supplier defs building the Claim57Residuals bundle from Johnson-regime data via Claim57Residuals.ofGraphExtractionHypotheses. Open inputs remain the caller hypotheses hx0/hsep/hcount/hlarge/hfactor (BCIKS20 SS5 Claim 5.6/5.7 side conditions + legacy Eq-5.12 factor-list bridge). Consumed downstream by CurvesBridge / Claim57FieldDischarge.
- papers: BCIKS20 SS5
### [PROVEN] claim57Residuals_of_gsInterpolant
- loc: `ArkLib/ToMathlib/Section5ConcreteJohnson.lean:113`
- Proven supplier: single z-independent Johnson budget natWeightedDegree Q 1 k < m*(n-ceil(delta*n)) transfers per-z via natWeightedDegree_one_k_eval_on_Z_le, feeding claim57Residuals_of_natCeil_johnson. Actively consumed (CurvesBridge.lean:698+, Claim57FieldDischarge.lean:470+).
### [PROVEN] strictCoeffPolysResidual_of_* producer-discharge family (8: _of_curveHenselDatum CurveFamilyHensel:143, _of_gsCurveInput CurveHenselSupply:662, _of_curveFamilyData FaithfulCurveExtraction:195, _of_faithful_frontier FaithfulFrontierComposition:298, _of_betaRec / _of_betaRec_offcentre / _of_betaRec_offcentreFin / _of_betaRecFin KeystoneStrictResidual:411,428,445,462, _of_section5DataOffcentreFaithful OffcentreFaithfulBundle:199, _of_section5DataOffcentreFin OffcentreKeystoneAssembly:247)
- loc: `ArkLib/ToMathlib/{CurveFamilyHensel,CurveHenselSupply,FaithfulCurveExtraction,FaithfulFrontierComposition,KeystoneStrictResidual,OffcentreFaithfulBundle,OffcentreKeystoneAssembly}.lean (10 thms)`
- All 10 are proven axiom-clean dischargers of StrictCoeffPolysResidual (BCIKS20/Curves.lean:2505) FROM a per-(u,P) producer hypothesis (BetaCurveInput*/CurveFamilyData/CurveHenselDatum/GSCurveInput/FaithfulFrontierData/Section5StrictDataOffcentre*). The single genuinely open surface underneath is the producer itself — the SS5 curve-extraction / gamma-is-a-root Hensel core. That is published math (BCIKS20 SS5 Steps 5-7 / Hab25), formalizable (effort L), currently blocked in-tree at the local-root/monicization frontier; every consumer is honestly conditional.
### [PROVEN] strictCoeffPolysResidual_zero
- loc: `ArkLib/ToMathlib/KeystoneStrictResidual.lean:478`
- Unconditional k=0 vacuity discharge (0<k antecedent), honest.
### [PROVEN] boundaryProbabilityResidual_of_strict
- loc: `ArkLib/ToMathlib/CurveFamilyRoundConsumers.lean:95`
- Unconditional in its regime: the boundary residual only fires on the branch not(delta < 1-sqrt(rho)); under strict radius the branch is unreachable (absurd). Legitimate branch-vacuity, lets faithful strict-regime producers fill both WHIR RoundKeystoneData residual fields.
### [PROVEN] L46 RS bricks (diffStackMCAResidualBelowUDR_rs:94, _of_two_mul_lt_card_sub:133, diffStackResidual_of_gsWitness L46GSLowerBound:187)
- loc: `ArkLib/ToMathlib/L46DiffStackRS.lean:94,133; L46GSLowerBound.lean:187`
- All three proven axiom-clean: ABF26 Lemma 4.6 hard direction below unique-decoding radius reduced to the single named witness Prop GSWitnessLowerBound C delta floor(delta*n) (L46GSLowerBound.lean:108, def only — no in-tree construction). The witness itself is BCIKS20 Prop 1.1-style deep-hole+GS-list construction: known math, provable (M/L), NOT the #232 prize regime (UDR, not past-Johnson).
### [PROVEN] BatchingConsistencyResidual (def) + batchingConsistencyResidual_sum
- loc: `ArkLib/ToMathlib/RSPhases.lean:128,133`
- Self-discharging: batchingConsistencyResidual_sum proves the residual by rfl at the canonical honest value; proven consumer batchingConsistency_of_residual in-file via sum_cube_MLE_mul. NOTE: zero consumers outside RSPhases.lean (file imported only by root ArkLib.lean) — RingSwitching (#29) wiring candidate or deletion candidate; not laundering, just unconsumed.
### [PROVEN] SpartanBricks self-discharged residual pairs (10: secondSumcheckTerminalEndpointResidual:474+_holds:482, finalCheckWithClaimValueRelResidual:677+_holds:685, secondSumcheckResidual:767+_holds:773, firstSumcheckResidual:779+_holds:785, r1csMleEncodingResidual:839+_holds:855)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:474-855`
- Each def is discharged in-file by a genuine _holds proof: terminal endpoint via polynomial eval + ring; valueRel via the endpoint bridge; first/second sumcheck existence via the actually-constructed firstSumcheckReduction/secondSumcheckReduction (liftContext of the proven sum-check); R1CS-MLE encoding via MvPolynomial.MLE_eval_scaled_sum. All in the #print axioms audit block.
### [PROVEN] SpartanBricks equivalence/weakening bridges (12: finalCheck...Residual_of_secondSumcheckTerminalEndpointResidual:693, secondSumcheck..._of_finalCheck...:703, ..._iff_...:715, composedCompletenessWithClaim{SecondSumcheckEval iff valueRel:1141, ValueRel_of_secondSumcheckEval:1157, SecondSumcheckEval_of_valueRel:1173, Residual_of_valueRel:1189, Residual_of_secondSumcheckEval:1213}, composedRbrKS WithClaim {iff:1294, of_secondSumcheckEval:1313, of_valueRel:1332, ValueRel_of_residual:1353, SecondSumcheckEval_of_residual:1388})
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:693-1388`
- Real implications, not pass-throughs: relation rewriting (finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn), Reduction.completeness_relOut_mono weakening, and for :1353 an explicit KnowledgeStateFunction reconstruction (toFun_full re-proved through probEvent_mono + subset). Axiom-audited in-file.
### [PROVEN] composedPIOPResidual:1019 + composedPIOPWithClaimResidual:1048 (+ _of_reduction packagers :1035,:1060)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1019-1060`
- DISCHARGED: composedPIOPResidual_holds_proof (ArkLib/ProofSystem/Spartan/Composition.lean:477) and composedPIOPWithClaimResidual_holds_proof (:482) witness the existence Props with the actually assembled composedPIOP_Rc (Composition.lean:367) / composedPIOPWithClaim_Rc. _of_reduction packagers are trivial-but-honest existential intros. NOTE the in-file comment block (~SpartanBricks:1014) still calls the composition 'sorry-gated' open engineering — STALE, should be refreshed to point at Composition.lean.
### [PROVEN] composedCompletenessResidual (def)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1077`
- DISCHARGED at the apex instance: Bricks.composedCompletenessResidual_proven_114c (ArkLib/ProofSystem/Spartan/ComposedCompletenessProven.lean:142) proves it for composedPIOP_Rc with ONLY standard honest-implementation side conditions (NeverFail init, support-faithful impl, state-preserving, never-fail impl). Grep- and statement-verified; axiom audit at file tail.
### [PROVEN] composedCompletenessWithClaimResidual (def)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1097`
- DISCHARGED: Bricks.composedCompletenessWithClaimResidual_proven (ArkLib/ProofSystem/Spartan/ComposedCompletenessWithClaimFinal.lean:30) = base proven_114c + prependClaim_perfectCompleteness + append_perfectCompleteness_keystone_empty_114, same honest-impl side conditions only.
### [PROVEN] 4 converter pass-throughs (composedCompletenessResidual_of_perfectCompleteness:1502, composedCompletenessWithClaimResidual_of_perfectCompleteness:1515, composedRbrKnowledgeSoundnessResidual_of_rbrKnowledgeSoundness:1534, composedRbrKnowledgeSoundnessWithClaimResidual_of_rbrKnowledgeSoundness:1549)
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1502-1549`
- Literal pass-throughs (:= hc / := hks; conclusion is defeq unfolding of hypothesis). SELF-DOCUMENTED as converters: file records the 2026-06-10 audit retiring the spartan_piop_* names that masqueraded as headline results, and points to the genuine dischargers (proven_114c, of_leaves). Harmless as named interfaces; must never be cited as end-to-end results.

**Pass-throughs found:**
- ArkLib/ToMathlib/SpartanBricks.lean:1502 composedCompletenessResidual_of_perfectCompleteness (:= hc)
- ArkLib/ToMathlib/SpartanBricks.lean:1515 composedCompletenessWithClaimResidual_of_perfectCompleteness (:= hc)
- ArkLib/ToMathlib/SpartanBricks.lean:1534 composedRbrKnowledgeSoundnessResidual_of_rbrKnowledgeSoundness (:= hks)
- ArkLib/ToMathlib/SpartanBricks.lean:1549 composedRbrKnowledgeSoundnessWithClaimResidual_of_rbrKnowledgeSoundness (:= hks)
- ArkLib/ToMathlib/FriComplete.lean:115 foldRound_perfectCompleteness (:= hResidual; conclusion = def-unfold of hypothesis)
- ArkLib/ToMathlib/FriComplete.lean:140 finalFoldRound_perfectCompleteness (:= hResidual)
- ArkLib/ToMathlib/SpartanRBRProof.lean:36 spartan_rbr_knowledge_soundness_checkpoint (self-documented honest hResidual -> hResidual checkpoint)
- (adjacent, found during audit) ArkLib/ProofSystem/Spartan/SpartanRBRWithClaimProof.lean:38 spartan_rbr_knowledge_soundness_with_claim (thin delegation to the :1549 pass-through)

**Laundering/vacuity findings:** No active deletion-laundering found in scope. Every docstring-claimed discharger was grep-verified to exist: deepHoleProbResidual_holds (CS25JointFar.lean:203), deepHoleJointFar_holds (:93), composedPIOPResidual_holds_proof / composedPIOPWithClaimResidual_holds_proof (ProofSystem/Spartan/Composition.lean:477,482), composedCompletenessResidual_proven_114c (ComposedCompletenessProven.lean:142), composedCompletenessWithClaimResidual_proven (ComposedCompletenessWithClaimFinal.lean:30), GSFactorData.MonicHighYResidual witness residualw (FaithfulFrontierWitness.lean:121). Structural protection: nearly every ToMathlib file ends with a #print axioms block naming its decls, so silent deletion breaks the build. THREE remediated historical incidents are documented in-file (good hygiene, keep): (1) SpartanBricks ~:1090 and ~:1247 record removed 'noncomputable constant' disguised axioms composedCompleteness_holds / composedRbrKnowledgeSoundness_holds; (2) SpartanBricks tail records the retired spartan_piop_* converter-masquerade names (external audit 2026-06-10); (3) ToMathlib/SpartanRBRProof.lean header records a removed fake '#114 breakthrough'. ONE STALE-DOC finding (reverse-laundering, understates progress): SpartanBricks.lean comment block before composedPIOPResidual (~:1005-1019) still claims the composition 'does not yet type-check', is 'sorry-gated (tracked by scripts/sorry_census.py)' — but composedPIOP_Rc exists and both existence residuals are discharged in Composition.lean; refresh the comment. VACUITY: the three *_zero discharges (k=0) and boundaryProbabilityResidual_of_strict are honest, explicitly-documented vacuity/branch-vacuity lemmas, not laundering. The 10 BoundaryDischarge bricks conclude Props refuted at concrete instances (not_boundaryCardResidual family) — files document the refutation and no consumer asserts the refuted Props unconditionally.

## ArkLib/ProofSystem/Logup/** — all 44 residual-named decls from AUDIT_LEDGER.md (lines 346–392), incl

### [PROVABLE (L)] SubPhaseSoundnessResidual (def)
- loc: `Security/Soundness.lean:118`
- Conjunction over midLanguage: sumcheck half PROVEN (sumcheckSoundnessResidual_pointwise); outer half = OuterSoundnessResidual (see below) — the single remaining genuine math item of #13 soundness.
- papers: Haböck ePrint 2022/1530 (LogUp) §grand-sum + Schwartz–Zippel
### [PROVABLE (L)] OuterSoundnessResidual (def) — hOuter@midLanguage, THE remaining #13 soundness blocker
- loc: `Security/SubPhaseSplit.lean:70`
- Mirror the PROVEN sharp-language template (outerSharpStateFunction + outerVerifier_rbrSoundness_sharp + marginalBridge_holds, OuterRbrSoundness.lean) but with state = zero-mid-claim over BOTH challenge rounds: round-1 flip bounded via outerBadChallenges_card_le, round-3 batch-challenge flip via card_filter_claimZero_mul_card_le + claim_not_identicallyZero (all PROVEN in OuterMaliciousClaim.lean:284,706,748). Then logup_soundness_pointwiseSumcheck (LogupSoundnessPointwise.lean:53) yields full headline soundness immediately. All bricks exist; remaining work is the 2-challenge RBR state function + per-round measure bookkeeping.
- papers: Haböck ePrint 2022/1530
### [PROVABLE (L)] AppendSoundnessResidual (def)
- loc: `Security/SubPhaseSplit.lean:108`
- Def is literally the full headline soundness statement (conclusion-alias). Holds once hOuter@midLanguage lands: logup_plainAppend_msg / append_soundness_msg (proven, axiom-clean) discharge the append seam given the two halves. Reduces 1:1 to OuterSoundnessResidual.
### [PROVABLE (L)] LogupSoundnessBrickResidual (def)
- loc: `Security/SubPhaseSplit.lean:115`
- = OuterSoundnessResidual ∧ (proven) ∧ (reduces to OuterSoundnessResidual). Single blocker as above.
### [PROVABLE (L)] [NOT IN LEDGER] issue13_soundness_sharp_outerDischarged — sharp-route apex
- loc: `Security/OuterRbrSoundness.lean:293`
- Conditional on: hRound (PROVEN: singleRound_oracleVerifier_rbrSoundness_canonical, SeqComposeRbrSoundness.lean:437), hError/hLast (bookkeeping), hProj@sharp (provably NOT a per-statement lens fact at the canonical inner language — same counterexample as corrected language; its probabilistic content belongs to the outer half, so the honest path is the midLanguage/pointwise route instead), and hAppend (binary plain-RBR append keystone — phase-1 proven, phase-2 = appendRbrSoundnessPhase2Residual, AppendRbrKeystone.lean:282; doomed-escape route mapped and knowledge-side template appendRbrKnowledgeSoundnessPhase2_subsingleton PROVEN under Subsingleton σ; plain-side assembly unfinished). Net: the pointwise route (single blocker hOuter@midLanguage) strictly dominates this route.
### [PROVABLE (L)] [NOT IN LEDGER] logup_soundness_pointwiseSumcheck — live soundness apex
- loc: `Security/LogupSoundnessPointwise.lean:53`
- Full headline LogUp soundness conditional ONLY on hOuter@midLanguage + 0<n + satisfiable impl conditions. Everything else (sumcheck half, append seam, oracle routing) proven. Closes #13 soundness the moment OuterSoundnessResidual lands.
- papers: Haböck ePrint 2022/1530
### [DEAD] sumcheckCompletenessResidual_of_honest_perRound
- loc: `Security/LogupCompletenessUncond.lean:159 (LEDGER STALE)`
- Decl no longer exists — the hHonest form was deleted as UNSATISFIABLE (dmvt audit) and replaced by sumcheckCompletenessResidual_of_perRound (:169, proven conditional on hPerRound). Update AUDIT_LEDGER entry.
### [DEAD] LogupSoundnessFullResidual (def)
- loc: `Security/LogupSoundnessClose.lean:170`
- Bundles hOuter@midSoundnessProtocolLanguage at paper error — REFUTED in typical regime by the tree's own prob_midSoundnessLanguage_ge_compl_support (OuterSoundnessSharp.lean:113: spurious roots of univ-cleared polynomial ⇒ uniform challenge lands in language w.p. ≈1 ≫ outerSoundnessError). Vacuously-conditional; superseded by sharp route (outerVerifier_soundness_sharp) and pointwise route. Keep only with a deprecation/refuted note, or delete with its consumer logup_soundness_full_of_residual.
### [DEAD] LogupSoundnessUncondResidual (def)
- loc: `Security/LogupSoundnessUncond.lean:241`
- Same refuted hOuter@midSoundnessProtocolLanguage conjunct as LogupSoundnessFullResidual; uninstantiable in typical regime; consumers (issue13_soundness_of_residual, logup_soundness_uncond_of_residual) are vacuously conditional. Deprecate in favor of sharp/pointwise.
### [PROVEN] SubPhaseCompletenessResidual (def)
- loc: `Security/Completeness.lean:237`
- Discharged by subPhaseCompletenessResidual_unconditional (SumcheckCompletenessUncond.lean:67) under only hInit:NeverFail + hImplSupp; instantiable (ZMod 5 witness in LogupCompletenessFinal.lean:126).
### [PROVEN] OuterCompletenessResidual (def)
- loc: `Security/SubPhaseSplit.lean:163`
- outerCompletenessResidual_of_neverFail (SubPhaseSplit.lean:252) ← outerOracleReduction_completeness (OuterCompleteness.lean:824), fully proved, no residual.
### [PROVEN] SumcheckCompletenessResidual (def)
- loc: `Security/SubPhaseSplit.lean:169`
- sumcheckCompletenessResidual_unconditional (SumcheckCompletenessUncond.lean:51): CubeFiber inner completeness + SumcheckLensProjComplete_unconditional; no hHonest (unsatisfiable form deleted).
### [PROVEN] AppendCompletenessResidual (def)
- loc: `Security/SubPhaseSplit.lean:183`
- appendCompletenessResidual_wired (LogupCompletenessWired.lean:184) via proven non-perfect msg-seam keystone OracleReduction.append_completeness_msg_proof; consumed end-to-end by logup_completeness_final.
### [PROVEN] LogupCompletenessBrickResidual (def)
- loc: `Security/SubPhaseSplit.lean:206`
- All three components discharged; apex logup_completeness_final (LogupCompletenessFinal.lean:71) + concrete instantiation logup_completeness_final_instantiable (:126). Completeness side of #13 is END-TO-END DONE.
### [PROVEN] subPhaseCompletenessResidual_iff_split / logupCompletenessBrickResidual_iff_subPhase_append / outerCompletenessResidual_of_neverFail
- loc: `Security/SubPhaseSplit.lean:174,213,252`
- Definitional Iff.rfl bridges + the proven outer discharge; all real.
### [PROVEN] OuterCompletenessRunResidual (def) + outerCompletenessRunResidual_proved + outerCompletenessRunResidual_iff
- loc: `Security/OuterCompleteness.lean:141,831,847`
- outerCompletenessRunResidual_proved (:831) discharges the def; iff is Iff.rfl.
### [PROVEN] OuterCompletenessRunFactsResidual (def) + outer_completenessRunFactsResidual
- loc: `Security/OuterCompleteness.lean:151,813`
- Both run facts proved: complement-zero via outer_perState_agree, failure bound via outer_completenessRun_failure_le (:801). No residual hypothesis.
### [PROVEN] outer_completeness_of_runResidual
- loc: `Security/OuterCompleteness.lean:211`
- Pass-through consumer (`h hInit`); kept as API; underlying residual now proven anyway.
### [PROVEN] subPhaseCompletenessResidual_of_sumcheck
- loc: `Security/OuterCompleteness.lean:840`
- Real reduction; its hSum input is since discharged by sumcheckCompletenessResidual_unconditional.
### [PROVEN] appendCompletenessResidual_iff_toReduction
- loc: `Security/LogupCompletenessClose.lean:139`
- Iff via proven verifier-fusion bridge (appendToReductionResidual_proof / oracleVerifier_append_toVerifier).
### [PROVEN] appendCompletenessResidual_wired
- loc: `Security/LogupCompletenessWired.lean:184`
- General non-zero-error append completeness discharged via append_completeness_msg_proof; bridge internal.
### [PROVEN] sumcheckCompletenessResidual_proved
- loc: `Security/SumcheckCompleteness.lean:45`
- Real conditional theorem (hPerRound + hInit + hImplSupp); strictly superseded by bridge-free sumcheckCompletenessResidual_unconditional — candidate for deprecation note, not deletion-critical.
### [PROVEN] sumcheckCompletenessResidual_holds
- loc: `Security/SumcheckCompletenessClose.lean:140`
- Conditional brick (hProj,hInner) — both inputs since discharged (SumcheckLensProjComplete_unconditional; oracleReduction_perfectCompleteness_unconditional); still the load-bearing transfer lemma.
### [PROVEN] sumcheckCompletenessResidual_unconditional + subPhaseCompletenessResidual_unconditional
- loc: `Security/SumcheckCompletenessUncond.lean:51,67`
- The unconditional completeness discharges (only hInit/hImplSupp standard data facts).
### [PROVEN] sumcheckCompletenessResidual_of_inner
- loc: `Security/SumcheckLensProjComplete.lean:122`
- hProj now a theorem (SumcheckLensProjComplete_unconditional :104); hInner input since discharged.
### [PROVEN] oracleReductionToReductionResidual_of_binary
- loc: `Security/BridgeAndAppendResiduals.lean:237`
- Real induction proof; its BinaryVerifierFusion input is now a theorem (binaryVerifierFusion_holds, LogupCompletenessUncond.lean:114, via proven oracleVerifier_append_toVerifier); hPerRound input bypassed entirely by the bridge-free completeness route.
### [PROVEN] SumcheckSoundnessResidual (def)
- loc: `Security/SubPhaseSplit.lean:78`
- Discharged OUTRIGHT by sumcheckSoundnessResidual_pointwise (SumcheckSoundnessPointwise.lean:134): pointwise rejection outside midLanguage ⇒ error-0 RBR ⇒ marginalBridge_holds; needs only 0<n + 3 satisfiable honest-impl conditions. No rbr-append keystone, no hProj, no hInnerRbr.
### [PROVEN] subPhaseSoundnessResidual_iff_split + logupSoundnessBrickResidual_iff_subPhase_append
- loc: `Security/SubPhaseSplit.lean:83,122`
- Iff.rfl / trivial repackaging.
### [PROVEN] issue13_sumcheckSoundnessResidual_projClosed
- loc: `Security/Issue13Status.lean:257`
- Real conditional re-export (hProj closed via SumcheckLensProjSound_holds, hMarginal via marginalBridge_holds; remaining hError/hInnerRbr inputs); strictly superseded by sumcheckSoundnessResidual_pointwise which needs none of them.
### [PROVEN] oracleAppendSoundnessResidual_of_plain
- loc: `Security/LogupSoundnessUncond.lean:117`
- Real content: rewrites the oracle-level append residual to the plain-verifier one via the proven binary fusion oracleVerifier_append_toVerifier. Generic and language-agnostic — used by the live pointwise route too.
### [PROVEN] logupAppendSoundnessResidual_of_plain
- loc: `Security/LogupSoundnessUncond.lean:166`
- Specialization of the above; theorem itself fine (the refuted-language typing lives only in its hOuter argument slot, mirrored by callers).
### [PROVEN] outerSoundnessResidual_real_of_marginal
- loc: `Security/OuterRunSamplesChallenge.lean:185`
- Conditional on OuterRunMarginalToUniform; that interface is discharged UNCONDITIONALLY for the real honest outer run by OuterRunSamplesChallenge_holds (OuterSoundnessReal.lean:383, full proof). Superseded by the sharp RBR route which needs no run-unfolding at all.
### [PROVEN] outerSoundnessResidual_real_of_runUnfolding
- loc: `Security/OuterSoundnessReal.lean:466`
- le_trans of the discharged OuterRunSamplesChallenge with proven outerSoundness_real (SZ math). Brick proven; consumed/superseded as above.
### [PROVEN] sumcheckSoundnessResidual_holds_of_rbr
- loc: `Security/RbrToSoundBridge.lean:264`
- Conditional theorem; its hMarginal slot since discharged by Verifier.marginalBridge_holds (MarginalBridgeProof.lean:374 — full real proof verified at source; the earlier deletion-laundering of this name is REPAIRED). Superseded by pointwise.
### [PROVEN] sumcheckSoundnessResidual_proved
- loc: `Security/SumcheckSoundness.lean:44`
- Honest conditional re-export of holds_of_rbr (4 named hyps); name slightly overclaims ("proved" = proved-modulo-named-hyps) but docstring is explicit. Superseded by pointwise.
### [PROVEN] sumcheckSoundnessResidual_holds
- loc: `Security/SumcheckSoundnessLift.lean:193`
- Conditional (hProj+hInnerRbr+hRbrToSound) liftContext transfer; every input since discharged or superseded (pointwise). Historical brick.
### [PROVEN] sumcheckSoundnessResidual_pointwise
- loc: `Security/SumcheckSoundnessPointwise.lean:134`
- THE live discharge of the embedded-sumcheck soundness half (error-0 RBR via pointwise rejection + marginalBridge_holds). Axiom-clean per file audit.
### [PROVEN] sumcheckSoundnessResidual_holds_projClosed
- loc: `Security/SumcheckSoundnessProjClosed.lean:109`
- hProj closed at canonical round-0 language (SumcheckLensProjSound_holds) + marginalBridge_holds; remaining hError/hInnerRbr. NOTE the file proves the corrected-language hProj variant is FALSE at that inner language (helpers≡0 counterexample) — important design fact. Superseded by pointwise.
### [PROVEN] sumcheckSoundnessResidual_holds_wired
- loc: `Security/SumcheckSoundnessWired.lean:88`
- hMarginal slot eliminated via marginalBridge_holds; remaining hError/hProj/hInnerRbr; language-parametric variants (sumcheckVerifier_soundness_forLang_wired) feed the sharp route. Superseded by pointwise for midLanguage.
### [PROVEN] [NOT IN LEDGER, decisive] outerVerifier_soundness_sharp — hOuter@SHARP DISCHARGED
- loc: `Security/OuterRbrSoundness.lean:252`
- NEW since memory snapshot (commit 86e18c7bf): protocol-level outer soundness at midSoundnessProtocolLanguageSharp with paper error, for any 2^n<|F|, via outerSharpStateFunction RBR + outerSoundness_sharp SZ + marginalBridge_holds. The malicious-prover outer-run wall was bypassed entirely (no run-unfolding).

**Pass-throughs found:**
- Logup.logup_soundness_of_residual — Security/Soundness.lean:133 (hAppendSoundness hypothesis = conclusion verbatim; honest residual-API pattern but zero content)
- Logup.logup_soundness_of_split — Security/SubPhaseSplit.lean:92 (same: hAppendSoundness = conclusion)
- Logup.AppendSoundnessResidual — Security/SubPhaseSplit.lean:108 (def is a conclusion-alias; makes the two above pass-throughs by construction)
- Logup.outerRunSamplesChallenge_of_marginal — Security/OuterRunSamplesChallenge.lean:171 (proof term is literally `hMarginal`; the two Props are defeq, recorded by the Iff.rfl at :152)
- Logup.outer_completeness_of_runResidual — Security/OuterCompleteness.lean:211 (proof = `h hInit`)
- Sumcheck.Spec.oracleVerifier_rbrSoundness — ProofSystem/Sumcheck/Spec/OracleRbrSoundness.lean:107 (returns its hSeqCompose hypothesis; documented; genuinely discharged later by oracleVerifier_rbrSoundness_of_round_append, SeqComposeRbrSoundness.lean:558)
- Logup.logupConcreteSumcheckOracleReduction_rbrSoundness — OracleRbrSoundness.lean:164 (same pass-through, specialized)
- Framework feeders consumed by Logup (outside dir): OracleVerifier.append_soundness, OracleReduction.append_completeness, Verifier.append_rbrSoundness (Append.lean:1018), Verifier.append_rbrKnowledgeSoundness — all return their explicit residual hypothesis (intentional residual-API; the msg-seam/completeness instances are now genuinely proven elsewhere, the plain-RBR append one is not)

**Laundering/vacuity findings:** (1) DOCSTRING-CLAIMS-WITHOUT-THEOREM: ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessPhase2Proof.lean — module docstring (lines 10–58) claims it "discharges the phase-2 half and assembles the unconditional keystone Verifier.append_rbrSoundness_keystone" and names "append_rbrSoundness_residual_msg below"; the 196-line file ends at StateFunction.appendDoomed_toFun_gt, `append_rbrSoundness_residual_msg` exists NOWHERE in the tree (grep), and append_rbrSoundness_keystone (AppendRbrKeystone.lean:320) is still conditional on appendRbrSoundnessPhase2Residual. The doomed-escape state-function bricks ARE real; the probabilistic assembly is absent. This gates the hAppend slot of every Logup sharp-route apex. Fix: finish the assembly (knowledge-side template appendRbrKnowledgeSoundnessPhase2_subsingleton at AppendRbrKnowledgeStateFunction.lean:1524 is proven and is the stated blueprint) or rewrite the docstring to WIP. (2) VACUOUS-CONDITIONAL SURFACE: hOuter@midSoundnessProtocolLanguage at paper error is refuted in the typical regime by the tree's own prob_midSoundnessLanguage_ge_compl_support (OuterSoundnessSharp.lean:113); consumers issue13_soundness, issue13_soundness_of_residual, issue13_soundness_msgSeam, issue13_soundness_msgSeam_wiredSumcheck, issue13_soundness_msgSeam_wiredRoundAppend, logup_soundness_full(/_of_residual), logup_soundness_uncond(/_of_residual), LogupSoundnessFullResidual, LogupSoundnessUncondResidual are all vacuously conditional. OuterSoundnessSharp.lean says so; Issue13Status.lean's headline docstring still advertises these as live front doors — update it to route readers to the sharp (outerVerifier_soundness_sharp) and pointwise (logup_soundness_pointwiseSumcheck) routes. (3) STALE LEDGER: AUDIT_LEDGER.md lists `sumcheckCompletenessResidual_of_honest_perRound` (LogupCompletenessUncond.lean:159) — that decl was honestly deleted (unsatisfiable hHonest, documented de-larp) and replaced by sumcheckCompletenessResidual_of_perRound (:169); ledger needs refresh. (4) REPAIRED PRIOR LAUNDERING CONFIRMED: Verifier.marginalBridge_holds (MarginalBridgeProof.lean:374) — previously deleted-but-docstring-claimed per project memory — now exists with a full 130-line real proof (read in full). (5) BUILD-STATE CAVEAT: machine axiom-verification was impossible in this audit (missing upstream RoundByRound.olean, LogupCompletenessFinal.olean; building forbidden); statuses rest on source reading + zero-sorry greps + in-file #print axioms audit blocks; recommend a fresh `./scripts/validate.sh` run before trusting axiom-cleanliness claims of the newest files (OuterRbrSoundness.lean, LogupCompletenessFinal.lean).

## ArkLib/OracleReduction/** — Composition/Sequential (26 ledger residuals + n-ary General.lean layer),

### [OPEN-RESEARCH] appendRbrKnowledgeSeamZeroResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeChallengeOracleLift.lean:44`
- Challenge-seam-only (V_to_P seam, i2=0) per-round flip bound. No generic discharger and none is possible: the seam-challenge flip probability is genuinely protocol-specific content (the bound rbrKnowledgeError2(0) depends on the protocol's challenge space). Honest end-state: keep named, discharge per instance (Spartan ComposedRbrKnowledgeSoundness threads it as hSeamZero explicitly - correct conditional usage). Msg-seam composition does not need it.
### [PROVABLE (L)] Verifier.appendKnowledgeSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:984`
- NO discharger exists anywhere in tree (grep confirms only def + 2 pass-through consumers + BCS conditional consumer). The straightline-KS append needs malicious-prover seam decomposition + extractor query-log routing (proveQueryLog.fst/verifyQueryLog). Cheapest route: replay the proven append_soundness_msg' seam machinery with the Extractor.Straightline.append (already proven, Append.lean Extractor section) and the runWithLog seam bricks (SeamDecompositionRunWithLog.lean). Alternative: route consumers through the proven rbr-KS keystone.
### [PROVABLE (M)] Verifier.appendRbrSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1008`
- Keystone append_rbrSoundness_keystone (AppendRbrKeystone.lean:320) discharges the det-V1 msg-seam case with phase-1 proven internally; only appendRbrSoundnessPhase2Residual remains (see that item). Once phase-2 lands the residual is discharged for the det-V1/Subsingleton-sigma/msg regime.
### [PROVABLE (M)] appendRbrSoundnessPhase2Residual
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKeystone.lean:282`
- Open named Prop, no discharger. The doomed-escape route is fully mapped and its bricks are PROVEN (StateFunction.doom:131, doom_toFun:147, appendDoomed:158, appendDoomed_toFun_le/gt:169/182, verify_notMem_lang_of_full_false:89 in AppendRbrSoundnessPhase2Proof.lean); remaining work = the probabilistic seam following the PROVEN knowledge-side template (appendRbrKnowledgeSoundnessPhase2_subsingleton + phase2_body_heq + simulateQ_run'_bind_of_subsingleton + Prover.sndAmnesiac), under Subsingleton sigma + msg seam. WARNING: file header is laundered (see launderingFindings).
### [PROVABLE (L)] OracleVerifier.appendKnowledgeSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1162`
- Same status as the plain Verifier.appendKnowledgeSoundnessResidual (no discharger); once plain lands, the proven toVerifier fusion transports it for free.
### [PROVABLE (M)] Lemma5_14HonestResidual + Lemma5_16HonestResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:648,655`
- No dischargers yet. Same shape as the proven 5.12: confine the honest fork/time bad events to BadEventDS.E using the dedup'd-trace engine in Lemma512Honest.lean / BadEvents.lean. Consumed by probEvent_honestBad_le_probEvent_E + honestBad_birthday_of_residuals (BirthdayBound.lean:362/436).
- papers: CO25 Lemmas 5.14/5.16
### [PROVABLE (M)] Lemma5_8EagerBirthdayResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BirthdayBound.lean:417`
- Open; the numeric bricks are already proven (birthday_toReal_le_lemma5_8Bound, hit_toReal_le_capacityRatio, lemma5_8Bound_eq_claim5_21Bound, all axiom-audited at file foot). Remaining = the 3 documented steps in the def's own docstring: eager-table fresh-uniform mediation via removeRedundantEntryDS, E = E_dup or E_func decomposition into capacity-segment families, per-flavor budget recombination into IsTotalQueryBound.
- papers: CO25 Lemma 5.8, sec 5.6
### [PROVABLE (L)] Hyb01StepResidual + Hyb12StepResidual + Hyb23StepResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaHybrids.lean:619,640,662`
- No dischargers. These are the CO25 sec 5.5-5.7 hybrid-step tvDist bounds. Hyb01's bad-event side is numerically closed conditional on 5.12/5.14/5.16/5.8 (honestBad_birthday_of_residuals); the coupling side of each step is unwritten. Hard but mapped engineering, not open math.
- papers: CO25 sec 5.5-5.7
### [PROVABLE (M)] Hyb34StepResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaHybrids.lean:681`
- Conditionally reduced in VerifierReplay.lean (~:905): discharged from two tvDist legs hA (Hyb3 vs Hyb3Strict) + hB (Hyb3Strict vs Hyb4 with eagerSimulatedProver) + numeric hsum into claim5_24Bound, via SPMF.tvDist_triangle. The two legs remain.
- papers: CO25 Claim 5.24
### [PROVABLE (L)] KeyLemmaEagerResidual + KeyLemmaResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:958 + KeyLemma.lean:241`
- KeyLemmaEagerResidual assembled from the four Hyb steps + proven budget residuals by keyLemmaEager_of_hybSteps (KeyLemmaAssembly.lean:98, also :131 strict-split variant) - proven conditional assembly. KeyLemmaResidual (CO25 Lemma 5.1, the apex) is consumed honestly as an explicit hypothesis by duplexSpongeToFSGameStatDist (KeyLemma.lean:267) and its docstring explicitly forbids trivial discharge. Closes once the Hyb chain closes. This is the largest remaining genuinely-open block in scope, but it is known math (CO25), not open research.
- papers: CO25 Lemma 5.1
### [PROVABLE (L)] BCSCompilerFrontierReady surface + bcs_compiler_preservation_residual_passthrough
- loc: `ArkLib/OracleReduction/BCS/BCSCompilerProof.lean:33 + BCS/Basic.lean:1420ff + FrontierBricks.lean`
- The pass-through is SELF-IDENTIFIED no-content ('Do not cite this as a result') - honest bookkeeping, keep or delete. BCSCompilerFrontierReady is an obligation bundle with proven intro/field/iff API (Basic.lean:1420-1562, FrontierBricks.lean) and zero consumers outside OracleReduction/BCS; no in-tree generic instance. The generic compiler preservation needs commitment binding/extractability content per instance; the #62 transparent-BCS end-to-end instance exists separately (CommitmentScheme/Transparent route). Append-side dependencies now discharged at msg seams (toReduction_soundness_of_append_msg residual-free, BCS/AppendSoundnessMsg.lean:73; completeness via BCSTransform_perfectCompleteness, CompletenessPreservation.lean:52).
- papers: BCS16
### [PROVABLE (S)] Verifier.liftContext_soundness
- loc: `ArkLib/OracleReduction/LiftContext/Reduction.lean:902`
- PASS-THROUGH (takes hLiftContextSoundness = its own conclusion). Notably the harder neighbors ARE genuinely proven: liftContext_knowledgeSoundness (:928), liftContext_rbr_soundness (:1425), liftContext_rbr_knowledgeSoundness (:1674) all construct the lifted extractor/state function for real. Plain soundness should be the easiest of the four - replay the rbr_soundness prover-projection argument without the state function (or derive from knowledgeSoundness shape). Oracle-level soundness/KS variants are visibly commented out in LiftContext/OracleReduction.lean (not laundering).
### [DEAD] ZKConcreteSimulatorKernel (+oracleReductionPublicRun, ZKConcretePublicView)
- loc: `ArkLib/OracleReduction/Security/Issue112Kernels.lean:55`
- Statement-only Prop ('zk_concrete_simulator_residual mathematics'); grep confirms ZERO consumers anywhere in tree (only ArkLib.lean import). Pure orphaned exploration from #112 - deletion candidate, or wire into the now-proven HVZK transfer stack if a use appears.
### [PROVEN] reductionAppendCompletenessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:901`
- Msg seam discharged: Reduction.append_completeness_msg (AppendSeamBridges3.lean:254, feeds appendStage1Bridge:64 + append_game_neverFail:97 + appendStage2Bridge:143 into append_completeness_msg_via_seamFactor) and append_completeness_msg_proof (AppendCompletenessNonPerfect.lean:133). Challenge-seam error-bearing path exists via append_completeness_challenge_via_seamFactor (AppendChallengeSeamChallenge.lean:373). Side conditions are honest-impl only (hInit NF, impl SP/NF/VB).
### [PROVEN] reductionAppendPerfectCompletenessResidual (+_of_message at AppendPerfectCompletenessMsg.lean:392)
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:920`
- Discharged for ALL seam cases: msg = append_perfectCompleteness_msg_proof (AppendPerfectCompletenessProof.lean:108) + reductionAppendPerfectCompletenessResidual_of_message (AppendPerfectCompletenessMsg.lean:392); challenge = append_perfectCompleteness_challenge (AppendPerfectCompletenessChallenge.lean:141); empty = append_perfectCompleteness_empty_proof (AppendPerfectCompletenessEmpty.lean:42). Side conditions: NeverFail init + state-independent-support impl.
### [PROVEN (S)] Verifier.appendSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:957`
- Msg seam discharged unconditionally: append_soundness_msg_residual (AppendSoundnessMsgProof.lean:440, via append_soundness_msg':230) under himplSP/himplNF/himplVB. Challenge-seam version not yet written but is 'provable' S-M using the proven #114 challenge-seam infra (evalDist_run'_challengeSeam_right, append_game_factor_challenge). BCS consumer made residual-free at msg seam by BCSCompiledPhases.toReduction_soundness_of_append_msg (BCS/AppendSoundnessMsg.lean:73).
### [PROVEN] Verifier.appendRbrKnowledgeSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1047`
- Discharged UNCONDITIONALLY for det-V1 + Subsingleton sigma + msg seam: append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional (AppendRbrKnowledgePhase2ReconcileProof.lean:349; hReconcile proven at :64). Challenge seam: append_rbrKnowledgeSoundness_keystone_subsingleton_challenge modulo the single hSeamZero residual. General carried-state sigma: open (3 obstructions: msg-seam, carried prover state, sigma-threading) - that general form is honest open research-grade engineering, all consumers in-tree are in the subsingleton regime.
### [PROVEN] OracleReduction.appendCompletenessResidual + appendPerfectCompletenessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1095,1116`
- Oracle layer collapses to plain layer via the unconditionally proven verifier fusion oracleVerifier_append_toVerifier (AppendToVerifierKeystone.lean:83) + appendToReductionResidual_proof (:148). PC discharged: append_perfectCompleteness_keystone (AppendToVerifierKeystone.lean:167, msg), append_perfectCompleteness_challenge_keystone (AppendChallengeKeystoneOracle.lean:64), append_perfectCompleteness_empty_keystone (AppendEmptyKeystoneOracle.lean:58), oracle challenge/empty also at AppendPerfectCompletenessOracleChallenge.lean:54/81.
### [PROVEN] OracleVerifier.appendSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1142`
- Reduced generically to the plain residual by OracleVerifier.oracleAppendSoundnessResidual_of_plain (ProofSystem/Logup/Security/LogupSoundnessUncond.lean:117 - generic namespace despite the file) via the proven fusion; plain msg-seam side proven (append_soundness_msg). Net: proven at msg seams; challenge seam inherits the plain-layer S-M gap.
### [PROVEN] OracleVerifier.appendRbrSoundnessResidual + appendRbrKnowledgeSoundnessResidual
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:1183,1205`
- rbr-KS: OracleVerifier.append_rbrKnowledgeSoundness_subsingleton (msg, via AppendRbrKnowledgeOracleLift) and append_rbrKnowledgeSoundness_subsingleton_challenge (AppendRbrKnowledgeChallengeOracleLift.lean:128, modulo hSeamZero) - proven in the subsingleton regime. rbr-Soundness oracle-level: gated on the plain phase-2 item (provable, M).
### [PROVEN] appendRunRightResidual + _holds_msg + _holds_empty
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:4112,4138 + EmptyAppend.lean:84`
- Syntactic right-block residual proven for msg seam (:4138) and n=0 (EmptyAppend.lean:84). At a challenge seam the SYNTACTIC equality is provably false by design (documented); the distributional version covers it. Not a gap.
### [PROVEN] appendRunRightResidualDist + _holds_msg + _holds_challenge
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRunEvalDist.lean:53,104 + AppendRunEvalDistChallenge.lean:265`
- Distribution-level run-factoring keystone discharged for BOTH seam directions (msg :104 via congrArg of the syntactic proof; challenge :265 via evalDist_bind_comm) plus empty. Prover.append_run is therefore fully closed at evalDist level - the original #433/#29 keystone.
### [PROVEN] appendToReductionResidual + _iff_verifier + _proof
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean:67,122 + AppendToVerifierKeystone.lean:148`
- appendToReductionResidual_proof discharges the bridge for EVERY pair of oracle reductions (given AppendCoherent instance), via _iff_verifier + oracleVerifier_append_toVerifier. Fully closed, no hypotheses beyond the coherence instance.
### [PROVEN] appendRbrKnowledgeSoundnessPerRoundResidual + appendRbrKnowledgeSoundnessPhase2Residual
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeStateFunction.lean:944,1226`
- PerRound discharged from phase2 at :1309; phase2 discharged under Subsingleton sigma + msg seam by appendRbrKnowledgeSoundnessPhase2_subsingleton (:1524) with hReconcile proven by appendRbrKnowledgePhase2SeamReconcile_proof (AppendRbrKnowledgePhase2ReconcileProof.lean:64). General non-subsingleton sigma remains open (carried-state obstruction) but every in-tree consumer is subsingleton.
### [PROVEN] n-ary seqCompose layer (General.lean) - genuine bricks
- loc: `ArkLib/OracleReduction/Composition/Sequential/General.lean:441,477 + SeqCompose*.lean`
- Real inductions exist beside the pass-throughs: seqCompose_perfectCompleteness_of_append (:441), seqCompose_completeness_of_append (:477), SeqComposeVerifierBricks (soundness/KS of_append :29/:59), SeqComposeMsgCompleteness (seqCompose_perfectCompleteness_msg :202 unconditional msg-chains), SeqComposeOracleCompleteness (:107/:147), and the headline n-ary rbr-KS for failing-det chains: Verifier.seqCompose_rbrKnowledgeSoundness_failingDet (SeqComposeRbrKnowledgeProof.lean:257) and OracleVerifier version (:365) with binaryVerifierFusionForRbrKnowledge_holds (:183). The 12 General.lean pass-throughs are dischargeable wholesale for failing-det/msg-first chains by these.
### [PROVEN] fiatShamir_runCollapseResidual (+_of_run_eq_honestExecution)
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:303,318`
- Discharged unconditionally by Reduction.fiatShamir_runCollapse (FiatShamir/BasicCompleteness.lean:150). FiatShamirRunCollapseProof.lean:34 'fiat_shamir_collapse_breakthrough' is just an alias to that proof (grandiose name, honest content). CompletenessUnroll.lean wrappers are superseded API.
### [PROVEN] fiatShamir_soundnessTransferResidual
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:893`
- Discharged for the canonical coupled implementation: fiatShamir_soundnessTransferResidual_canonical (StateRestorationTransport.lean:899, srInit/fiatShamirCoupledQueryImpl). The def quantifies over arbitrary impl pairs; for non-coupled pairs it is intentionally statement-only (the coupled instance is the semantically meaningful one). #116 closed.
### [PROVEN] fiatShamir_knowledgeSoundnessTransferResidual
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:1002`
- fiatShamir_knowledgeSoundnessTransferResidual_canonical (StateRestorationTransport.lean:3301) - SR=>FS knowledge transfer with explicit extractor (fiatShamirStraightlineExtractorOfStateRestoration), canonical coupled impl. #116 closed.
### [PROVEN] fiatShamir_statisticalHVZKTransferResidual + 5 bridge lemmas (.mono_error/.of_zero/.of_perfectTransfer/.of_statistical_zero/_iff_statistical_zero)
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:1159-1332`
- Canonical discharge: fiatShamir_statisticalHVZKTransferResidual_canonical_proved (HVZKCanonicalClose.lean:79) at every error budget, from the perfect transfer. The 5 bridges are proven API lemmas over the named Props.
### [PROVEN] fiatShamir_hvzkTransferResidual
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:1286`
- fiatShamir_hvzkTransferResidual_canonical_proved (HVZKKernelClose.lean:1080) - UNCONDITIONAL for canonicalFSInit/canonicalFSImpl, via proven coupling kernels (canonicalFSPerStateCoupling_proved, canonicalFSCouplingKernel_proved). HVZKTransferReduction.lean:315/:343 are the proven conditional reductions it feeds. ZKResidualBridge.lean:55/68/81 are proven equivalence bridges. #116 fully closed.
### [PROVEN] duplexSpongeFiatShamir_runCollapseResidual + Salted variant
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Completeness.lean:200,212`
- Both discharged unconditionally: duplexSpongeFiatShamir_runCollapse (RunCollapse.lean:60) and duplexSpongeFiatShamirSalted_runCollapse (:96).
### [PROVEN] 4 simulator budget residuals (SimulatedProverChallengeBudget, SimulatedProverSharedBudget, D2sQueryStepGSpecBudget, D2fOuterImplSharedBudget)
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:921,938,997,1013`
- All four discharged unconditionally in SimulatorBudgets.lean: simulatedProverChallengeBudget (:672), simulatedProverSharedBudget (:743), d2sQueryStepGSpecBudget (:395), d2fOuterImplSharedBudget (:514). CO25 Lemma 5.1 conjuncts (a)/(b) query-budget side.
- papers: CO25
### [PROVEN] Lemma5_12HonestResidual
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:641`
- Discharged: lemma5_12_honest (Lemma512Honest.lean:178) via the hasInvEntry_implies_E keystone.
- papers: CO25

**Pass-throughs found:**
- Reduction.seqCompose_completeness — General.lean:408
- Reduction.seqCompose_perfectCompleteness — General.lean:422
- Verifier.seqCompose_soundness — General.lean:518
- Verifier.seqCompose_knowledgeSoundness — General.lean:533
- Verifier.seqCompose_rbrSoundness — General.lean:630
- Verifier.seqCompose_rbrKnowledgeSoundness — General.lean:649 (dischargeable NOW for failing-det/Subsingleton-σ chains by SeqComposeRbrKnowledgeProof.lean:257)
- OracleReduction.seqCompose_completeness — General.lean:670
- OracleReduction.seqCompose_perfectCompleteness — General.lean:685
- OracleVerifier.seqCompose_soundness — General.lean:707
- OracleVerifier.seqCompose_knowledgeSoundness — General.lean:727
- OracleVerifier.seqCompose_rbrSoundness — General.lean:745
- OracleVerifier.seqCompose_rbrKnowledgeSoundness — General.lean:770 (dischargeable NOW by SeqComposeRbrKnowledgeProof.lean:365)
- OracleVerifier.seqCompose_toVerifier — General.lean:~237 (hSeqComposeToVerifier-taking; genuine fusion proven in SeqComposeRbrKnowledgeProof.lean:192 via binaryVerifierFusionForRbrKnowledge_holds:183)
- Reduction.reduction_append_completeness — Append.lean:909 (hResidual-taking)
- Reduction.reduction_append_perfectCompleteness — Append.lean:927
- Verifier.append_soundness — Append.lean:964
- Verifier.append_knowledgeSoundness — Append.lean:992
- Verifier.append_rbrSoundness — Append.lean:1018
- Verifier.append_rbrKnowledgeSoundness — Append.lean:1057
- OracleReduction.append_completeness — Append.lean:1104
- OracleReduction.append_perfectCompleteness — Append.lean:1124
- OracleVerifier.append_soundness — Append.lean:1151
- OracleVerifier.append_knowledgeSoundness — Append.lean:1171
- OracleVerifier.append_rbrSoundness — Append.lean:1193
- OracleVerifier.append_rbrKnowledgeSoundness — Append.lean:1216 (hResidual-taking, as flagged in task)
- BCSCompiler.bcs_compiler_preservation_residual_passthrough — BCS/BCSCompilerProof.lean:33 (self-identified identity on hReady)
- Verifier.liftContext_soundness — LiftContext/Reduction.lean:902 (hLiftContextSoundness-taking; NOT previously in the known list)
- Reduction.fiatShamir_soundness_of_stateRestoration + fiatShamir KS/HVZK '_of_' wrappers — FiatShamir/Basic.lean (residual-implication-taking, honest conditional shape, all now fed by proven canonical closes)

**Laundering/vacuity findings:** THREE findings. (1) SERIOUS — AppendRbrSoundnessPhase2Proof.lean header (lines 8-22) claims "This file discharges the phase-2 half ... and assembles the unconditional keystone Verifier.append_rbrSoundness_keystone ... The discharge of that residual under these side conditions is `append_rbrSoundness_residual_msg` below". Repo-wide grep: theorem append_rbrSoundness_residual_msg DOES NOT EXIST anywhere; the 196-line file ends at the doomed-escape bricks (appendDoomed_toFun_gt:182). The header also cites a nonexistent `append_rbrSoundness_keystone_ofPhase2Residual` (real name: append_rbrSoundness_keystone). The doomed-escape obstruction analysis and bricks are real and proven, but the claimed probabilistic discharge was never written — classic docstring-claims-without-theorem. Fix: rewrite the header to say bricks-only, or actually prove the seam (effort M, knowledge-side template exists). (2) STALE-DOC — AppendSeamBridges.lean header (lines 38-42) lists appendStage1Bridge/appendStage2Bridge/append_game_neverFail/append_completeness_msg as "the discharged" content of this file, but the file only proves appendStage₁_run_eq_liftM; the four theorems actually exist in AppendSeamBridges3.lean (64/143/97/254) — claims are TRUE repo-wide but point at the wrong file (this matches the MEMORY.md prior finding; Bridges3 has since landed, so it downgraded from laundering to stale pointer). Also note AppendSeamBridges.lean:173 and AppendSeamBridges2.lean:145 both declare appendStage₁_run_eq_liftM (duplicate-name dedup candidate). (3) COSMETIC — FiatShamirRunCollapseProof.lean `fiat_shamir_collapse_breakthrough` (author "Master Cryptographer") is a one-line alias to the genuine Reduction.fiatShamir_runCollapse; content honest, naming theatrical; could be folded into BasicCompleteness.lean. NO vacuity found: spot-checked residual defs (appendSoundnessResidual, phase-2 residuals, KeyLemmaResidual, Lemma5_8) are real quantified statements over arbitrary provers/computations, not vacuously-true Props; KeyLemma.lean explicitly documents that its residual "can not be discharged by trivial". Zero sorry/admit/axiom in scope confirmed (only doc-comment mentions).

## ArkLib/ProofSystem/Whir/** (38 files, 17 ledger residuals + statement-only surfaces), Stir/** (30 fi

### [OPEN-RESEARCH] mca_johnson_bound_CONJECTURE (def Prop)
- loc: `ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:319`
- ACFY24 Conjecture 4.12 (Johnson, BStar=√ρ, exact errStar) — the live target. NOT discharged in general; MCAConjectureStatus.lean correctly mandates it stay conjecture-shaped. In-tree state: (a) vacuous small-field discharge proven (mca_johnson_bound_CONJECTURE_smallField); (b) pair-case (parℓ=2) fully reduced to the Hab25/BCIKS20 §5 surfaces — per-δ JohnsonNumericBound, Claim-1 cells, StrictCoeffPolysResidual(Large), RawGSCargo (MCAConjecturePairReduction + MCAJohnsonBound); pair case is provable-L if the Hab25 §5 formalization (hImprove weld, Z-degree budget, S11 — Data/CodingTheory scope) is completed (paper proof exists: Hab25). General-ℓ at the exact constants remains a literature conjecture. Honest end-state: named Prop + conditional consumers only — currently satisfied.
- papers: ACFY24 §4.3 (Conj 4.12), Hab25, BCIKS20 §5
### [OPEN-RESEARCH (M)] GenMutualCorrParams (assumption-carrying class, field h : hasMutualCorrAgreement)
- loc: `ArkLib/ProofSystem/Whir/Folding.lean:683 and ArkLib/ProofSystem/Whir/RBRSoundness.lean:85`
- Category (c)/(d): no instance anywhere (grep-verified); consumed as free hypothesis by Folding Thm 4.20, whir_rbr_soundness, WhirBricksConstruction. Instantiating field h at BStar=√ρ IS Conjecture 4.12 — open. NEW ROUTE NOW AVAILABLE: a UDR-window instance (BStar i=(1+ρᵢ)/2, errStar=|ιᵢ|/|F|) is constructible from mca_rsc_pair_holds since hcard pins parℓ=2 — provable, effort M; would make the WHIR chain consumable end-to-end in the unique-decoding regime. Honest conditional design otherwise; keep.
- papers: ACFY24 Conj 4.12 (√ρ) / BCIKS20 (UDR instance)
### [PROVABLE (L)] whir_rbr_soundness (def Prop, WHIR Thm 5.2)
- loc: `ArkLib/ProofSystem/Whir/RBRSoundness.lean:185`
- Statement-only existential front door, honest DISPOSITION docstring. It already THREADS the MCA data as hypothesis {h : GenMutualCorrParams}, so its remaining content given that data is: real WHIR verifier construction + IsSecureWithGap with the per-round budget — paper math (ACFY24 §5/ABF26 §4), not open research. Route: instantiate via whirCheckedVectorIOP (real checks + completeness PROVEN, CheckedVerifier.lean:585) + a sub-1-budget rbr proof from h.errStar; the per-round fold leg is Folding L4.21–4.23 (proven as implications) + the Thm 4.20 composite. Deepest item in scope. Conditional dischargers today: whir_vector_iop_breakthrough (pass-through), whir_rbr_soundness_of_whirVectorSpec_secure_gap (ToMathlib).
- papers: ACFY24 §5, ABF26 §4
### [PROVABLE (L)] folding_listdecoding_if_genMutualCorrAgreement (def Prop, ABF26 Thm 4.20)
- loc: `ArkLib/ProofSystem/Whir/Folding.lean:795`
- Open statement-only Prop; honest disposition. Ingredients all proven in-file: union-bound backbone (Pr_le_finset_sum_of_implies), L4.21/4.22/4.23 (folding_preserves_listdecoding_base/_bound/_base_ne_subset, repaired with paper-faithful hsub/hrev hypotheses), deterministic fold algebra (fold_f_g_poly). Remaining: the k-fold inductive composite of the single-step lemmas under params.h — standard given an MCA instance. Stale docstring at :728 says the capstone 'remains sorry' — it is a def Prop, no sorry exists.
- papers: ABF26 §4 / ACFY24 L4.20–4.23
### [PROVABLE (L)] stirCheckingRbrSoundnessResidual (def Prop)
- loc: `ArkLib/ProofSystem/Stir/CheckingVerifier.lean:963`
- The genuine #301 soundness leg for the REAL checking verifier. Proven discharges: vacuous-budget (stirCheckingRbrSoundness_of_one_le_first :1117, explicit no-security-content note) and small-field |F| ≤ (m−1)|ι| with δ ≤ (1−ρ)/2 (of_small_field :1200, via one_le_proximityError_of_card_le :1156). General large-field sub-1-budget case: open in-tree but paper math exists (ACFY24stir Lemma 5.4 per-round analysis from BCIKS20 CA); route = prove stirCheckingCABridge (below) + the in-tree BCIKS20 §5 residual completion. Effort L.
- papers: ACFY24stir §5 (L5.4), BCIKS20 §4–5
### [PROVABLE (L)] stirCheckingCABridge (def Prop)
- loc: `ArkLib/ProofSystem/Stir/CheckingVerifier.lean:981`
- The implication (∀k StrictCoeffPolysResidual + PerRoundProximityGap) → checking-verifier rbr KS — the isolated #301 protocol-soundness math. Discharged only in small-field (stirCheckingCABridge_of_small_field :1215, trivially via the vacuous conclusion; NO fake instance exists anywhere — grep-verified, the HonestAxioms fake-instantiation mentioned in the brief is absent from the entire git history of this repo). General case: per-round flip-probability analysis of the fold/out/shift/fin checks against the Johnson-CA quantities — known paper math, real multi-file Lean effort (knowledge state function tracking per-round proximity, like the landed InitRbrSoundness but with nonzero error rounds). Effort L.
- papers: ACFY24stir §5, BCIKS20
### [PROVABLE (L)] stir_main + stir_rbr_soundness (def Props, Thm 5.1 / Lemma 5.4 front doors)
- loc: `ArkLib/ProofSystem/Stir/MainThm.lean:117,176`
- Statement-only existential front doors with honest 2026-06-10 STATUS notes. Conditional witnesses landed: stir_rbr_soundness_of_{secure_vectorIOP,stirVSpec_secure_gap,checkingIOP_CA/card_le/e7/large/small_field}, stir_main_of_{secure_vectorIOP,residuals,checkingIOP_*} (all exist, grep-verified). small_field route consumes NO soundness residual (cc82a99b3) but pins secpar=0. Remaining unconditional content = stirCheckingCABridge (L, above) + the numeric complexity legs (M, proof-length/query-count arithmetic; Complexity.lean has only the M=0 stub M_bound). Genuine δ∈(0,1−1.05√ρ) security needs the Johnson-regime BCIKS20 residuals.
- papers: ACFY24stir Thm 5.1/L5.4
### [PROVABLE (M)] queryRoundPerfectCompletenessResidual
- loc: `ArkLib/ProofSystem/Fri/Spec/Completeness.lean:29`
- Open in-tree, no discharger, no external consumer; companion theorem queryRound_perfectCompleteness (:39) is a literal pass-through (:= hResidual). Math is standard honest-FRI query-round completeness; the run-unrolling infra now exists (unroll_n_message keystone used by Stir/Whir completeness proofs). Effort M.
- papers: BBHR18 (FRI) completeness
### [PROVABLE (L)] foldPhasePerfectCompletenessResidual
- loc: `ArkLib/ProofSystem/Fri/Spec/Completeness.lean:52`
- Open; pass-through wrapper foldPhase_perfectCompleteness (:65) := hResidual; its hRounds/hFinal arguments are themselves the still-open ToMathlib residuals foldRoundPerfectCompletenessResidual / finalFoldRoundPerfectCompletenessResidual (FriComplete.lean:106,131) AND are unused binders in the Prop body (vacuous decoration — worth cleaning). Route: per-round fold completeness via foldf/PolySplit algebra + seqCompose/append perfect-completeness keystones (#433 append_perfectCompleteness_msg_proof and the #114 challenge-seam bricks are landed). Effort L (multi-round seqCompose threading).
- papers: BBHR18
### [PROVABLE (M)] reductionPerfectCompletenessResidual
- loc: `ArkLib/ProofSystem/Fri/Spec/Completeness.lean:84`
- Open; the entire 'Brick D' chain is pass-through plumbing: reduction_perfectCompleteness (:111) routes through reduction_perfectCompleteness_of_phases (ToMathlib/FriCompleteCompose.lean:72) whose body is literally `exact hResidual`, discarding the hFold/hQuery hypotheses. Given the two phase residuals, this is exactly the binary-append completeness keystone instance — the keystone is proven (#433/#114), so this should now be M: apply OracleReduction append completeness to reductionFold ++ queryOracleReduction.
### [PROVABLE (L)] fri_query_soundness (def Prop, Claim 8.2 batched-FRI residual)
- loc: `ArkLib/ProofSystem/BatchedFri/Security.lean:870`
- Named residual Prop, honest docstring (CA-density → jointAgreement of the batch). Proven discharges: complete-codeword extreme (of_forall_mem :896), jointProximity bridge (:926), and the small-field UNCONDITIONAL routes (QuerySoundnessSmallField.lean:50,96 — residual hypotheses PROVED not assumed, vacuous-threshold regime). General large-field case gated on StrictCoeffPolysResidual/BoundaryCardResidual (the #304 band) + the transcript-semantics jointAgreement witness — paper math known (BCIKS20 §8 batching + correlated agreement). Effort L.
- papers: BCIKS20 §8
### [PROVABLE (L)] fri_soundness (def Prop, Claim 8.3 lift)
- loc: `ArkLib/ProofSystem/BatchedFri/Security.lean:1574`
- Same shape as fri_query_soundness one level up: ~20 proven conditional front doors (…_of_queryRoundDensityBoundAndBatchedFRIOracleLens[And{JointProximity,AffineLineCA,RSAffineLine,AffineSpaceCA,CurveCA,SequentialComposition,TotalError,PhaseErrorBounds}]), plus fri_soundness_of_card_le_curve unconditional in the small-field regime. Proven local bricks: queryRoundAcceptanceBound_holds (:433), queryRoundDensityBound_holds (:465), batchedFRIOracleLensReduction_holds (:496, rfl). Open inputs: the same BCIKS20 residual band + virtual-oracle-lens soundness-preservation (library frontier) + OracleVerifier.appendSoundnessResidual. Effort L.
- papers: BCIKS20 §8
### [DEAD] mca_capacity_bound_CONJECTURE (def Prop)
- loc: `ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:363`
- Doubly dead: (1) the genuine up-to-capacity MCA claim is REFUTED in the literature (CS25/BCHKS25/DG); (2) the Lean formalization is VACUOUSLY TRUE as written — unbounded ∃ c₁ c₂ with no <1 constraint, proven trivially by MCACapacityTrivial_keep.lean:19 (c₁=0, c₂=|F|). Only consumer is that triviality demo. Keep as historical record per its own docstring, or delete both; either way it carries zero proof obligation. Note: both files' 'NOT in build' docstrings are stale (ArkLib.lean:1035,1445 import them).
### [DEAD] whirVectorIOP_rbrKnowledgeSoundness_dummy (def Prop)
- loc: `ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:70`
- Superseded: ThresholdKSF's indicator discharge is strictly sharper than the all-one budget this def asks for (and its docstring claim that 'even the all-one budget is not discharged merely by noting probabilities ≤1' is now stale — the indicator KSF construction does exactly the missing extractor/state-function work). Only consumer is whirVectorIOP_isSecureWithGap_dummy_of_rbr in the same file. Deletion candidate (or rewire to the indicator theorem).
### [DEAD] stirMultiRoundRbrSoundnessResidual (def Prop, shell verifier)
- loc: `ArkLib/ProofSystem/Stir/MultiRoundAssembly.lean:222`
- Residual for the SHELL verifier (verify = pure true); CheckingVerifier.lean:958 itself flags it 'likely-false' for sub-1 budgets (the shell accepts everything). Superseded by stirCheckingRbrSoundnessResidual. Sole consumer: stirMultiRoundIOP_isSecureWithGap (:229) in the same file, itself only general wiring. Deletion candidate once the checking front doors are the sole route; at minimum its docstring should carry the likely-false warning that currently lives only in CheckingVerifier.
### [DEAD] STIR.proximity_gap (def Prop, Thm 4.1 front door)
- loc: `ArkLib/ProofSystem/Stir/ProximityGap.lean:77`
- FALSE as stated (free GenFun; instantiate GenFun=0 — documented in its own STATUS block) and inert (no consumers). The honest repaired versions exist and are PROVEN: proximity_gap_of_residuals (ProximityGapProof.lean:34, GenFun pinned to monomials, gated on the named §5/§6.2 residuals) and proximity_gap_of_card_le (ProximityGapSmallField.lean:21, unconditional small-field). Either delete the defective def or repair its statement to the monomial generator.
### [PROVEN] 13 MCAConjecturePairReduction reduction bricks (mca_johnson_bound_CONJECTURE_pair_of_{johnsonNumericBound,claim1_cells,decode_family_pinning,decode_family_window,fixed_linear_factor_cells,coeff_polys_cells}, decode_family_affine_pinning_of_*, hsteps57_of_* ×6)
- loc: `ArkLib/ProofSystem/Whir/MCAConjecturePairReduction.lean:98–819`
- All proven axiom-clean conditional implications (in-file #print axioms; header records [propext, Classical.choice, Quot.sound]); they pin the entire pair-case open surface onto the named Data-side residuals (JohnsonNumericBound, StrictCoeffPolysResidual(Large), RawGSCargo, Claim-1 cells). Upstream dependency theorems verified to exist (hsteps57_of_window @ Hab25CaptureKernelUD.lean:227, johnsonBoundReal_le_errStar_real @ Hab25ConjectureGlue.lean:90).
### [PROVEN] mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo
- loc: `ArkLib/ProofSystem/Whir/MCAJohnsonBound.lean:37 (ledger says :49; actual decl :37)`
- Proven conditional composition (hL/hInput/hdata hypotheses carry the open GS/Hab25 §5 producer content). File title 'Final Johnson MCA Bound Discharge' slightly oversells — it is a conditional bridge, not a discharge; body is honest.
### [PROVEN] mca_johnson_bound_CONJECTURE_smallField
- loc: `ArkLib/ProofSystem/Whir/MCAJohnsonSmallField.lean:27`
- Vacuous-regime discharge: |F| ≤ (parℓ−1)·2^{2m}·10⁷ forces errStar ≥ 1. Honest docstring; 'NOT in build' note is stale (imported at ArkLib.lean:1440). Import probe of this module succeeded.
### [PROVEN (M)] mca_rsc (def Prop, Cor 4.11) — pair instance
- loc: `ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:291; discharged at ArkLib/ProofSystem/Whir/MCARscPairUDR.lean:62`
- mca_rsc_pair_holds proves the LITERAL mca_rsc at parℓ=Fin 2, exp=(0,1) unconditionally (hyps only 2^m ≤ |ι|, exp j = j): BStar=(1+ρ)/2 makes the admissible band exactly the unique-decoding window, errStar=|ι|/|F| matched via epsMCA_rs_udr_le_full (MCAUDRBound.lean:338, exists) + epsMCACurve_two_eq_epsMCA + the curve seam. This is the real content behind the recent 'UNCONDITIONAL pair-generator MCA on the unique-decoding window' commits — verified genuine, but it is the UDR regime, NOT the √ρ conjecture. General-parℓ mca_rsc remains open in-tree: provable (BCIKS20 UDR CA for Vandermonde stacks + the proven per-row→symmetric reconciliation proximityCondition_imp_relDist), effort M–L.
- papers: BCIKS20 Thm 1.2/§4 (UDR), ACFY24 Cor 4.11
### [PROVEN] hasMutualCorrAgreement_genRSC_pair_of_window
- loc: `ArkLib/ProofSystem/Whir/Hab25WindowMCA.lean:45`
- Unconditional pair MCA at the conjecture's exact errStar on the window 2n+2^m ≤ 3⌈B*·n⌉ (B*⪆2/3, hence UD-ish radius). Composes johnsonNumericBound_of_window' (Hab25WindowCount.lean:110, exists) with johnsonBoundReal_le_errStar_real. Real but regime-limited; does not advance the √ρ surface. Could not re-run #print axioms (Hab25Core.olean missing due to concurrent churn); in-file #print axioms directive present.
### [PROVEN] whirVectorIOP_perfectCompleteness (def Prop)
- loc: `ArkLib/ProofSystem/Whir/Protocol.lean:45`
- Discharged: whirVectorIOP_perfectCompleteness_holds (ProtocolCompleteness.lean:125; replica ThresholdKSF.lean:415) — pure-true shell verifier, completeness is real but easy. CHECKED-verifier analogue also PROVEN: whirCheckedVectorIOP_perfectCompleteness(_whirRelation) (CheckedVerifier.lean:585/658), via the run-support invariant paperProver_runToRound_invariant; import probe of CheckedVerifier succeeded.
### [PROVEN] whirVectorIOP_rbrKnowledgeSoundness (def Prop) + whirVectorIOP_isSecureWithGap (def Prop)
- loc: `ArkLib/ProofSystem/Whir/Protocol.lean:55,66; discharged at ThresholdKSF.lean:282,299,424`
- Discharged ONLY at the indicator budget (1 at finalRandomnessChallengeIdx, 0 elsewhere) via the genuinely reusable ThresholdKSF machinery (thresholdKSF + rbrKnowledgeSoundness_indicator, all side conditions proven). HONESTY: unit budget at one round = no security content, and the underlying verifier is the pure-true shell; docstrings say so. The meaningful sub-1-budget obligation lives on whirCheckedVectorIOP_isSecureWithGap_of_rbr (CheckedVerifier.lean:667, hSound consumed as hypothesis) and is gated on the MCA chain: open-research at √ρ, provable (M–L) on the UDR window using mca_rsc_pair_holds.
### [PROVEN] Whir keystone/budget brick families: WhirRbrKeystone, epsRbr accounting, keystone_curves_bound(_of_remainingCore/_of_card_le/_e7), perRoundProximityGap_*, whirRbrShape_of_secure, MCAJohnson{ErrStar,ErrStarBounds,Envelope,TrivialRegime,HardRegime,Reduction,MutualExtract,JointAgreement,CurveExtract,CurveJoint,Uniqueness}, MCA{PairSeam,CurveSeam,AffineLineGenerator}, PairGeneratorSeam, Hab25WhirBridge, MCAConjectureEllaryReduction
- loc: `ArkLib/ProofSystem/Whir/{KeystoneReduction,KeystoneSmallField,RbrBudgetAccounting,ProtocolSoundness:42,MCAJohnson*,MCAPairSeam,MCACurveSeam,MCAAffineLineGenerator,PairGeneratorSeam,Hab25WhirBridge,MCAConjectureEllaryReduction}.lean`
- Large family of proven, axiom-clean bricks over the named Data-side open Props (StrictCoeffPolysResidual, BoundaryProbabilityResidual, BCIKS20RemainingCore, JohnsonNumericBound, epsMCA bounds). Each is a real implication/seam/arithmetic lemma; none fabricates a discharge. The open surface they all sit on is the Hab25/BCIKS20 §5 residual family (out of this audit's scope, Data/CodingTheory).
### [PROVEN] strictCoeffPolysResidual_all_of_card_le / _card_le_e7 / _of_large
- loc: `ArkLib/ProofSystem/Stir/CheckingVerifier.lean:1008,1030,1052`
- Proven adapter bricks: discharge the ∀k residual family from the in-tree BCIKS20 small-field/e7/large-sector theorems (strictCoeffPolysResidual_of_card_le(_e7), strictCoeffPolysResidual_of_large). Pure plumbing, honest.
### [PROVEN] Stir proven completeness/structure chain: stirRoundReduction_completeness, stirInitReduction_rbrKnowledgeSoundness, stirCheckingIOP_perfectCompleteness, stirMultiRoundIOP_perfectCompleteness, MultiRound/VectorBridge/FullChain/Round3*/Block*
- loc: `ArkLib/ProofSystem/Stir/RoundCompleteness.lean:200; InitRbrSoundness.lean:109; CheckingVerifier.lean:882; MultiRoundAssembly.lean; VectorBridge/FullChain/Round3{Block,Completeness,Compose}/Block(s)Completeness/RoundVector*`
- The #301 mechanical layer is real: the def-Prop obligation stirRoundReduction_completeness (RoundProtocol.lean:196) is DISCHARGED by stirRoundReduction_completeness_proved; zero-error rbr KS of the initial block landed (a5611eb65); checking-IOP perfect completeness proven for symbolic M. Stale docstrings: RoundProtocol.lean:190 still says 'proof owed/sorry' — discharged in the sibling file.
### [PROVEN] Fri/Spec/Soundness end-to-end chain (reduction_soundness_totalError etc.)
- loc: `ArkLib/ProofSystem/Fri/Spec/Soundness.lean:146–408`
- Assembly theorems proven as implications, conditional on per-round soundness hypotheses + the OracleReduction-scope named seam residual OracleVerifier.appendSoundnessResidual (free hypothesis h_residual). Caveat: foldRounds_seqCompose_soundness (:146) is a pass-through (hypothesis h_seq is verbatim the conclusion). The per-round soundness facts themselves (BCIKS20-accounted roundError) have no in-tree proof — they are consumed as h_round hypotheses; open content = same BCIKS20 CA surface + appendSoundnessResidual (partially closed by AppendSoundnessMsgProof per memory, challenge-seam variants remain).
### [PROVEN] BatchedFri brick files (QueryRoundAnalysis, QueryRoundProbability, QueryRoundRS{AffineLine,Curve}Soundness, CosetInjectivity, Spec/*)
- loc: `ArkLib/ProofSystem/BatchedFri/*.lean`
- Proven projection/adapter bricks routing the Data-side BCIKS20 residual hypotheses into the Security.lean front doors; no fabricated instances found (residuals always appear as explicit hypotheses).

**Pass-throughs found:**
- Fri.Spec.Completeness.queryRound_perfectCompleteness — ArkLib/ProofSystem/Fri/Spec/Completeness.lean:39 (`:= hResidual`, conclusion = residual body)
- Fri.Spec.Completeness.foldPhase_perfectCompleteness — ArkLib/ProofSystem/Fri/Spec/Completeness.lean:65 (`:= hResidual`; also its hRounds/hFinal args are unused binders inside the residual def)
- Fri.Spec.Completeness.reduction_perfectCompleteness — ArkLib/ProofSystem/Fri/Spec/Completeness.lean:111, routed through Fri.Spec.reduction_perfectCompleteness_of_phases (ToMathlib/FriCompleteCompose.lean:72) whose body is `exact hResidual` and discards hFold/hQuery
- Fri.Spec.foldRounds_seqCompose_soundness — ArkLib/ProofSystem/Fri/Spec/Soundness.lean:146 (hypothesis h_seq is verbatim the conclusion)
- WhirIOPP.whir_vector_iop_breakthrough — ArkLib/ProofSystem/Whir/WhirVectorIOPProof.lean:24 (takes π + hSecure ≈ the conclusion's existential content; pure ∃-packaging; the name 'breakthrough' overclaims — confirms the #113 closed-overstated audit)
- whirVectorIOP_isSecureWithGap_holds — ArkLib/ProofSystem/Whir/Protocol.lean:77 (`:= ⟨hComplete, hSound⟩`, pair packaging)
- StirIOP.MultiRound.stirCheckingRbrSoundness_of_CA — ArkLib/ProofSystem/Stir/CheckingVerifier.lean:992 (`:= hBridge hCA hPR`, modus ponens over the named bridge — honest but zero content)
- stir_rbr_soundness_of_stirVSpec_secure_gap / stir_rbr_soundness_of_secure_vectorIOP / stir_main_of_secure_vectorIOP — ArkLib/ProofSystem/Stir/RbrFrontDoor.lean:31, MultiRoundAssembly.lean:252,340 (anonymous-constructor ∃-packaging front doors; honestly documented as such)

**Laundering/vacuity findings:** No deletion-laundering found in scope: every theorem name claimed in scope docstrings exists (verified stirCheckingIOP_perfectCompleteness:882, stir_main_of_checkingIOP_{CA:1518,card_le:1553,small_field:1659}, stirCheckingCABridge_of_small_field:1215, hsteps57_of_window, johnsonNumericBound_of_window', epsMCA_rs_udr_le_full, etc.). The 'deleted HonestAxioms.lean' fake-instantiation files from the brief are absent from this repo's entire git history (`git log --all -- '*HonestAxioms*'` empty); critically, NO instance/theorem in the current tree discharges stirCheckingCABridge or mca_johnson_bound_CONJECTURE outside the honest vacuous/small-field regimes — both Props are back to honest unproven. VACUITY: (1) mca_capacity_bound_CONJECTURE as formalized is trivially true (unbounded ∃ c₁ c₂, no <1 constraint — proven by MCACapacityTrivial_keep.lean), so the Lean def does not encode the refuted literature conjecture; (2) all ThresholdKSF/indicator and stirCheckingRbrSoundness_of_one_le_first discharges are unit-budget — no security content, docstrings honest; (3) STIR.proximity_gap is false-as-stated (free GenFun), documented and inert. STALE DOCSTRINGS (not laundering, fix-worthy): MCAJohnsonSmallField.lean:17 + MCACapacityTrivial_keep.lean:9 say 'NOT in build' but both are imported (ArkLib.lean:1440,1035); Folding.lean:728 says Thm 4.20 'remains sorry' (it is a def Prop); RoundProtocol.lean:190 says completeness 'proof is sorry/owed' (discharged at RoundCompleteness.lean:200); ThresholdKSF.lean:319 says ProtocolCompleteness 'not in the current build graph' (it is, ArkLib.lean:1449). COMMIT-MESSAGE OVERCLAIM: f92931808 'Whir: finalize wiring for rbrKnowledgeSoundness and Johnson MCA bound (#302)' touches no Whir file and discharges nothing — it adds an OracleReduction challenge-seam brick and swaps `fun _ => rfl` for `PerRoundProximityGap.refl` in Stir/CheckingVerifier.

## ArkLib/ProofSystem/Binius/** — 13 'class *Residual : Prop' decls in BinaryBasefold (per AUDIT_LEDGER

### [PROVABLE (L)] FoldPreservesBBFCodeMembershipResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:992`
- Asserts: 1-step fold of a BBF codeword (additive-NTT RS code, level i) lands in code at i+1 (DP24 Lem 4.13 consequence). The analytic core is ALREADY PROVEN+built: fold_advances_evaluation_poly_step and iterated_fold_advances_evaluation_poly (Reconstruct/IteratedFoldAdvances.lean:68,364, olean built, in-file #print axioms). Remaining: general-i novel-basis reconstruction (every deg<2^(ℓ−i) poly = intermediateEvaluationPoly i coeffs; CompPoly AdditiveNTT only has i=0 intermediate_poly_P_base) + degree bound of intermediateEvaluationPoly, then glue with proven exists_BBF_poly_of_codeword (Code.lean:64). Legacy full proof retained as block comment above the class. Consumed by iterated_fold_preserves_BBF_Code_membership_nat (Code.lean:1044+) and Soundness/Lift.lean:40 (variable-bound, honest).
- papers: DP24 eprint 2024/504 §4 (Lem 4.13); BaseFold eprint 2023/1705
### [PROVABLE (M)] FoldMatrixDetNeZeroResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1968`
- Asserts: every 2^steps fold matrix M_y is nonsingular. Crux base case PROVEN: baseFoldMatrix_det_ne_zero (BaseFoldDetBrick.lean:75, det = x₁−x₀ = basis_x 0 ≠ 0, built+axiom-clean). Remaining: recursive block factorization det = ±(x₁−x₀)^{2^n}·det M₀·det M₁ induction over foldMatrixNat structure. Consumed by foldMatrix_det_ne_zero (Prelude.lean:1981) → Proposition4_21.lean:69,96,484 (nested inside Prop421Case1 residual hypothesis).
- papers: DP24 2024/504 §4.2
### [PROVABLE (M)] FinalSumcheckStepLogicCompleteResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1363`
- Asserts IsStronglyComplete of finalSumcheckStepLogic. A FULL twin proof exists in-tree: FRIBinius finalSumcheckStep_is_logic_complete (FRIBinius/CoreInteractionPhase.lean:1075) proves the analogous (ring-switching-context) statement outright with the exact same skeleton; the BinaryBasefold stale direct proof is retained as comment below the class (blocker: 'generated oracle-output equality' rot). Port the FRIBinius pattern back. Consumed by Steps/FinalSumcheck.lean:162 (finalSumcheckOracleReduction_perfectCompleteness).
- papers: DP24 2024/504 §4
### [PROVABLE (M)] ExtractMLPCorrectnessResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean:207`
- Asserts extractMLP f = some tpoly ↔ firstOracleWitnessConsistencyProp (tpoly's base codeword within UDR of f) at i=0; pure Berlekamp–Welch decoder correctness transported across the sDomain↔Fin enumeration. The BW correctness base EXISTS proven: decoder_eq_some / hammingDist_le_of_decoder_eq_some / not_exists_of_decoder_eq_none (ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:79,95,136); extractMLP (Basic.lean:773) already routes through that decoder via sDomainFinEquiv. Remaining = cardinality/equiv glue + UDR arithmetic. Consumed by firstOracleWitnessConsistencyProp_unique, Steps/Fold.lean:775, Steps/FinalSumcheck.lean:1362/1776, BBFSmallFieldIOPCS.lean:184/190, FRIBinius/CoreInteractionPhase.lean:1495.
- papers: DP24 2024/504 §3; classical BW
### [PROVABLE (L)] Prop4212Case1Residual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:230`
- Asserts DP24 Prop 4.21.2 Case 1 (fiberwise-close) incremental bad-event bound ≤ |S^dest|/|L|: per-quotient-point degree-1 Schwartz–Zippel (nondegenerate via butterfly-matrix invertibility) + union bound over the disagreement set. ORIGINAL FULL PROOF BODY retained verbatim as block comment after the class; blocker is reworking fiberwiseDisagreementSet witness extraction against the post-split quotient-map API (old iteratedQuotientMap_succ_comp bridge dropped). Known math, pure re-mechanization. Consumed by prop_4_21_2_incremental_bad_event_probability (Incremental.lean:1394) → Steps/Fold.lean:1623 (fold-round RBR-KS doom-escape bound).
- papers: DP24 2024/504 Prop 4.21
### [PROVABLE (L)] PreTensorCombineMultilinearResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:823`
- Asserts iterated_fold f = multilinearCombine(preTensorCombine_WordStack f, r) — pure tensor-decomposition algebra. Blocker precisely documented: bit-reversal mismatch between legacy challengeTensorProduct (LSB) and multilinearWeight (MSB), see Prelude.lean:1916 note. Route: either prove the bit-reversal-permuted matrix-form bridge, or fresh induction via iterated_fold_first + multilinearCombine_recursive_form_first (both named in docstring as existing). Consumed by iterated_fold_eq_multilinearCombine_preTensorCombine (Incremental.lean:1075).
- papers: DP24 2024/504 §4.2
### [PROVABLE (M)] FoldPreTensorCombineAffineSplitResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:967`
- Asserts ⋈|preTensorCombine(fold f r) = affineLineEvaluation(⋈|U_even, ⋈|U_odd, r) (one fold step = affine line on LSB even/odd split). The even/odd tensor identities (h_tensor_even/h_tensor_odd) are LIVE PROVEN code immediately above the class (EvenOddSplit section, Incremental.lean ~600-805); docstring says old direct proof 'too brittle / kernel-times out' — proof-engineering, not math. Consumed by fold_preTensorCombine_eq_affineLineEvaluation_split → Case-2 restoration path (Incremental.lean:1173+).
- papers: DP24 2024/504 §4.2
### [PROVABLE (S)] FoldEqMultilinearPreTensorStep1Residual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:1077`
- steps=1 specialization of PreTensorCombineMultilinearResidual (fold f r = multilinearCombine U (fun _ => r)); docstring: only 'fragile Fin ℓ coercions' block the direct specialization. Smallest item in the family; also discharged automatically once the general residual is proven. Consumed at Incremental.lean:1228.
- papers: DP24 2024/504
### [PROVABLE (M)] PreTensorCombineJointProximityResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:1120`
- Asserts DP24 Lemma 4.22 close branch: fiberwiseClose f ⟹ preTensorCombine word within UDR of interleaved destination code. Proof plan in docstring; key ingredient ALREADY PROVEN: preTensorCombine_is_interleavedCodeword_of_codeword (Soundness/Lift.lean:188, built olean). Remaining = the fiber-projection Hamming-distance bound Δ₀(⋈|pTC f, ⋈|pTC g) ≤ Δ₀(f,g). Consumed at Incremental.lean:1171/1250/1296 (Case-2 assembly).
- papers: DP24 2024/504 Lem 4.22
### [PROVABLE (L)] Prop4212Case2Residual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean:1315`
- Asserts Prop 4.21.2 Case 2 (fiberwise-far) incremental bound ≤ |S^dest|/|L| via DG25 affine proximity gap. NOT gated on open proximity-gap research: the needed within-UDR gap theorems are PROVEN axiom-clean in-tree (verified by #print axioms: ReedSolomon_ProximityGapAffineLines_UniqueDecoding, DG25/ReedSolomon.lean:38; affine_gaps_lifted_to_interleaved_codes, DG25/MainResults.lean:887; both [propext,Classical.choice,Quot.sound]); the Binius-side bridge affineProximityGap_RS_interleaved_contrapositive (Incremental.lean:84) is also fully proven. lemma_4_21_interleaved_word_UDR_far (Lift.lean:346) and the even/odd non-closeness lemma are proven. Remaining gap (per docstring): the s=0 boundary of the commented-out fiberwiseClose_fold_implies_affineLineEval_close ([NeZero steps] vs ϑ−(k+1)=0) — handle the final step separately where fiberwiseClose degenerates to plain UDR closeness. Conditional on residuals #7/#9 above.
- papers: DP24 2024/504 Prop 4.21; DG25 (in-tree, proven)
### [PROVABLE (L)] Prop421Case1FiberwiseCloseResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Proposition4_21.lean:66`
- Non-incremental Prop 4.21 Case 1: Pr[fiber disagreement set not preserved under steps-fold] ≤ steps·|S_next|/|L|. Same SZ+union-bound math as Prop4212Case1; ORIGINAL PROOF BODY retained as block comment after the wrapper (Proposition4_21.lean:117+). Note: its holds-field itself takes [FoldMatrixDetNeZeroResidual] — nested conditionality, discharge #2 first. Consumed by prop_4_21_bad_event_probability (Proposition4_21.lean:484+).
- papers: DP24 2024/504 Prop 4.21
### [PROVABLE (L)] Prop421Case2FiberwiseFarResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Proposition4_21.lean:436`
- Non-incremental Prop 4.21 Case 2: Pr[iterated fold of a fiberwise-far word lands within UDR] ≤ steps·|S_next|/|L|. Needs the same three bridges as the incremental Case 2 (far→interleaved-distance = Lift.lean lemma proven; DG25 specialization proven; iterated_fold/multilinearCombine = residual #6). Once #6/#9/#10 land this follows the docstring plan. Consumed by prop_4_21_bad_event_probability.
- papers: DP24 2024/504 Prop 4.21; DG25 (in-tree)
### [PROVABLE (S)] PreviousSuffixFiberAlignmentResidual
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:568`
- Asserts extractSuffixFromChallenge at block source j·ϑ = getFiberPoint at the extractMiddleFinMask index — pure index/basis bookkeeping, no new math. Its docstring calls the key lemma 'the former iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask', but that lemma EXISTS LIVE AND PROVEN at QueryPhase.lean:317 (general i/steps, coefficient computation fully mechanized). QueryPhasePrelims is upstream of QueryPhase in the import graph, so move/duplicate that proof into QueryPhasePrelims (its ingredients getSDomainBasisCoeff_of_iteratedQuotientMap / qMap_total_fiber_repr_coeff live in Prelude) and weld the 0+k vs k cast (extractSuffixFromChallenge_congr_destIdx already exists for the transport). Cheapest discharge of the 13. Consumed by logical_checkSingleRepetition_guard_eq / queryBlockSourceSuffix_maps_to_destSuffix (QueryPhasePrelims.lean:698,814) → QueryPhaseSoundness.lean:283/462/807.
- papers: DP24 2024/504 §4.4

**Pass-throughs found:**
- foldRelayOracleReduction_perfectCompleteness — BinaryBasefold/CoreInteractionPhase.lean:159 (proof = exact hFoldRelayPerfectCompleteness)
- foldRelayOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:200
- foldCommitOracleReduction_perfectCompleteness — CoreInteractionPhase.lean:259
- foldCommitOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:305
- nonLastSingleBlockOracleReduction_perfectCompleteness — CoreInteractionPhase.lean:866
- lastBlockOracleReduction_perfectCompleteness — CoreInteractionPhase.lean:898
- sumcheckFoldOracleReduction_perfectCompleteness — CoreInteractionPhase.lean:918
- lastBlockOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:948
- nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:998
- nonLastBlocksOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:1039
- sumcheckFoldOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:1072
- coreInteractionOracleReduction_perfectCompleteness — CoreInteractionPhase.lean:1137
- coreInteractionOracleVerifier_rbrKnowledgeSoundness — CoreInteractionPhase.lean:1174
- fullOracleReduction_perfectCompleteness — BinaryBasefold/General.lean:117 (exact hFullProtocolCompleteness at :134)
- fullOracleVerifier_rbrKnowledgeSoundness — BinaryBasefold/General.lean:149 (exact hFullProtocolRbrKnowledgeSoundness at :165)
- FRIBinius fullOracleReduction_perfectCompleteness — FRIBinius/General.lean:191 (:= hAppendPerfectCompleteness)
- FRIBinius fullOracleVerifier_rbrKnowledgeSoundness — FRIBinius/General.lean:237 (:= hAppendRbrKnowledgeSoundness)
- bbf_fullOracleReduction_perfectCompleteness — BBFSmallFieldIOPCS.lean:765 (final hypothesis hFullAppendPerfectCompleteness ≡ conclusion modulo RingSwitching wrapper; effective pass-through)
- bbf_fullOracleVerifier_rbrKnowledgeSoundness — BBFSmallFieldIOPCS.lean:832 (same hypothesis-forwarding family). NOTE: all are openly documented as intentional ('Residual surface' headers in CoreInteractionPhase.lean:41 and General.lean:21) — the real obligation behind every one is the append/seqCompose security-composition keystone family (#433); honest end-state is to wire the repo's proven append keystones in, until then every Binius apex security claim is 100% assumption at the composition layer.

**Laundering/vacuity findings:** FOUR findings. (1) LATENT BUILD BREAKAGE FROM THE HonestAxioms DELETION (most important): the 13 classes have NO instances anywhere (verified incl. multiline grep), but at least 5 consumer files invoke the residual-gated wrapper lemmas WITHOUT binding the typeclasses: Steps/Fold.lean (:775/:780 ExtractMLP…, :1623 prop_4_21_2_incremental… which my olean probe shows carries SIX residual instance binders), Steps/FinalSumcheck.lean (:162, :1362, :1776), Soundness/QueryPhaseSoundness.lean (:283/:462/:807), BBFSmallFieldIOPCS.lean (:184/:190), FRIBinius/CoreInteractionPhase.lean (:1495). I verified the Lean semantics with a minimal vanilla replica (/tmp/lean_semantics_probe.lean): term-mode wrappers DO inherit the variable instance binder, and a consumer without the instance fails with synthInstanceFailed. So these files compiled only while the deleted untracked HonestAxioms.lean supplied (false-axiom) instances; they cannot re-elaborate now. Consistent evidence: .lake oleans exist exactly for the modules that bind their residuals (Prelude, Code, Relations, Spec, Reconstruct/*, Soundness/{Lift,Proposition4_21,Incremental,FoldDistance}, BaseFoldDetBrick) and are ABSENT for the entire consumer cone (Steps/*, QueryPhasePrelims→QueryPhaseSoundness, ReductionLogic, CoreInteractionPhase, General, QueryPhase, BBFSmallFieldIOPCS, FRIBinius/{CoreInteractionPhase,General}). The 'zero sorry/axiom' state is therefore only honest at statement level; a clean lake build will fail in ProofSystem/Binius. Fix is mechanical (S): add the matching variable [<class> …] binders to those files so the conditionality propagates visibly. (2) FRIBinius/General.lean:491 fullOracleVerifier_knowledgeSoundness presents an apex concrete knowledge-soundness theorem (DP24 Construction 5.1) but its Step-1 invokes the pass-through fullOracleVerifier_rbrKnowledgeSoundness (:237) WITHOUT supplying its required explicit hypothesis hAppendRbrKnowledgeSoundness — under Lean named-arg eta-expansion this cannot typecheck; the theorem is at best latently broken and in any honest repair must become conditional. (3) Ghost docstring references: Code.lean:975-976 cites classes IteratedFoldLastResidual / IteratedFoldMatrixFormResidual as existing convention precedents; neither exists anywhere in the tree (mild deletion-laundering of names, no proof claimed). (4) Inverse laundering: QueryPhasePrelims.lean:560 docstring claims iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask is 'former'/dropped, but it is live and fully proven at QueryPhase.lean:317 — the docstring understates available infrastructure and hides the cheapest residual discharge (item 13). No instance of a docstring claiming a *Residual is discharged was found; the 13 class docstrings are honest about being unproven.

## ArkLib/ProofSystem/Spartan/** (12 ledger items + non-ledger surfaces), Sumcheck/** (2), Plonk, BCS, 

### [OPEN-RESEARCH] winningSetSoundness_le_toySoundnessError_mcaSafe_residual
- loc: `ArkLib/ProofSystem/ToyProblem/Leaderboard.lean:355 (not in ledger — lowercase name evaded the regex)`
- ABF26 Lemma 6.10 winning-set bound with an ε_mca(C,δ) term — this is the #232 MCA surface. Up-to-capacity reading DISPROVEN (CS25/BCHKS/DG, eprint 2025/2046) so it must never be discharged at capacity; the Johnson-radius variant (BStar=√ρ) is provable in principle but requires ground-up Johnson/Guruswami–Sudan/RS list-decoding formalization absent from mathlib (genuine L+ project, not a port). Honest end-state already in place: named Prop, all consumers (Leaderboard.lean:377,485,656; ToMathlib/KoalaIRSAccounting.lean) take it as explicit hypothesis, docstring says DISPROVEN+NEEDS_CLASSICAL. CANNOT be closed as stated for general δ.
- papers: ABF26 L6.10; eprint 2025/2046; Johnson/GS
### [PROVABLE (M)] composedCompletenessResidual_proven (full apex, no leaf hypotheses)
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompletenessFinal.lean:88`
- NOT currently machine-checked: module has NO olean and cannot compile because its import FirstChallengeComplete.lean is build-broken (verified by lake env lean: unknown identifier `ofPFunctor_toPFunctor` at 131, ambiguous `map_pure` at 142, failed simulateQ rewrite at 152, all inside firstChallenge_perfectCompleteness). All five leaf theorems it cites DO exist and 4/5 live in built modules (sendEvalClaim_perfectCompleteness ComposedCompletenessLeaves.lean:171 [olean]; linearCombination_perfectCompleteness_sendEvalClaimBF LinearCombinationComplete.lean:177 [olean]; prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF ComposedCompletenessLeaves.lean:532 [olean]; finalCheck_perfectCompleteness_leaf FinalCheckLeafComplete.lean:132 [olean]). Route: repair the 3 mathlib bit-rot errors in FirstChallengeComplete.lean (rename/replace ofPFunctor_toPFunctor, qualify _root_.map_pure, re-seam one erw), then rebuild.
### [PROVABLE (M)] composedCompletenessResidual_proven_114c
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompletenessProven.lean:142`
- Duplicate of ComposedCompletenessFinal apex (the _114c parallel assembly with its own finalCheck_perfectCompleteness_leaf_114c). Same blocker: imports build-broken FirstChallengeComplete.lean. After repair, keep ONE of {ComposedCompletenessFinal, ComposedCompletenessProven} and delete the other (confirmed near-identical role).
### [PROVABLE (S)] composedCompletenessResidual_of_two_leaves
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompletenessTwoLeaves.lean:46`
- Fails to compile on its OWN error (verified): 'declaration contains universe level metavariables' in the application of composedCompletenessResidual_of_five_leaves.{0, ?u, u_2}. Fix: pin the universe arguments explicitly (e.g. .{0,0,0}) or make linearCombination_perfectCompleteness_sendEvalClaimBF's universe explicit. Trivial repair; deps all have oleans.
### [PROVABLE (S)] composedCompletenessWithClaimResidual_proven
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompletenessWithClaimFinal.lean:30`
- Sound assembly (base apex + prependClaim_perfectCompleteness + append_perfectCompleteness_keystone_empty_114) but transitively blocked: imports ComposedCompletenessFinal which imports broken FirstChallengeComplete. Unblocks automatically after the FirstChallengeComplete repair.
### [PROVABLE (M)] firstChallenge_perfectCompleteness (+ _consumer, _leaf wrappers)
- loc: `ArkLib/ProofSystem/Spartan/FirstChallengeComplete.lean:98 (wrappers: ComposedCompletenessFinal.lean:76, FirstChallengeLeaf.lean:58)`
- The proof script exists and is a direct run-unfold (RandomQuery lift, both relation endpoints rfl-bridged) but the module is bit-rotted: 3 concrete errors (ofPFunctor_toPFunctor renamed upstream; map_pure ambiguity; one erw simulateQ_bind no longer fires). FirstChallengeLeaf.lean and PhaseCompletenessLeaves.lean are transitively unbuildable (verified). This is THE single blocking repair for the entire composed-completeness apex chain.
### [PROVABLE (M)] hSeamZero x2 = Verifier.appendRbrKnowledgeSeamZeroResidual (challenge-seam flip bound at i2=0)
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeChallengeOracleLift.lean:44 (consumed at ComposedRbrKnowledgeSoundness.lean:391,579,587,709,717)`
- Genuinely open in-tree (no *_holds; grep-verified consumed only as hypothesis) but actively being closed: f60eb2129 discharged the companion hReconcile; d042399fc (HEAD-1) landed phase2_body_heq_challenge_zero (the body-factoring half: append_runToRound seam factoring at i2=0, axiom-clean). Remaining: the 'zero-RECONCILE' (trivial-prefix reconcile at the seam) + feeding it through the discharge. Subsingleton σ ambient (already required by the Spartan consumer) dissolves the known σ-threading obstruction.
### [PROVABLE (L)] 8 Spartan per-phase rbr-KS leaves (h1..h8 of the composed rbr-KS fold)
- loc: `hypotheses of ComposedRbrKnowledgeSoundness.lean:626`
- No Spartan-instance rbr-KS leaf theorems exist yet (grep-verified). Route: the two sum-check phases lift the proven generic sumcheck rbr-KS (oracleVerifier_rbrKnowledgeSoundness, Sumcheck/Spec/SingleRound.lean, error deg/|R|) through the first/second-sumcheck lenses (lens-coherence instances already proven for completeness); the five 0/1-round forwarding phases (firstMessage, firstChallenge, sendEvalClaim, linearCombination, prependRLCTargetKS, finalCheck) are pure-deterministic verifiers (toVerifier_pure proven) with error 0 — routine per-phase KSF constructions. SumcheckRbrKSResidualAnalysis.lean:34 (residualImplication, proven brick) documents that the naive lift_knowledgeSound route for the FIRST sumcheck is FALSE per-instance (one-point vanishing does not imply R1CS-sat), so the first-sumcheck leaf must carry the witness through the relation chain, not re-derive R1CS-sat — known design, not open math.
- papers: Setty20 (Spartan)
### [DEAD] oracleReductionToReductionResidual (sumcheck verifier-fusion 'bridge')
- loc: `ArkLib/ProofSystem/Sumcheck/Spec/OracleCompleteness.lean:54`
- Superseded AND suspected false-as-stated: the per-round reduction (SingleRoundBridge.lean) bottoms out in hSimpleBridge = '(Simple.oracleReduction).toReduction = Simple.reduction', explicitly documented as the 'false oracleReduction_eq_reduction' (the two verifiers check different objects). The genuine apex is the bridge-FREE proven theorem oracleReduction_perfectCompleteness_unconditional (OracleCompletenessUncondCorrect.lean:33, olean built, via proven CubeFiber coh_proven_inst) — no bridge anywhere. Remaining consumers of the bridge Prop (OracleCompletenessUncond.lean, SingleRoundBridge.lean, Spartan/SpartanSumcheckUnconditional.lean) are a legacy conditional chain; deletion candidates as a unit. FirstSumcheckBridgeFree/SecondSumcheckBridgeFree already route the Spartan consumers around it.
### [DEAD] oracleReductionToReductionResidual_of_perRound (+ binaryVerifierFusion_proof)
- loc: `ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessUncond.lean:85`
- Proven implication brick (olean built, binary fusion side genuinely discharged via oracleVerifier_append_toVerifier) but over the superseded suspected-false bridge Prop; nothing on the live path consumes it. Legacy — delete with the bridge chain or keep as historical reduction.
### [DEAD] WholeZkVMResidual
- loc: `ArkLib/ProofSystem/ZkVMBoundary.lean:109`
- Documentation template, zero in-tree consumers (grep-verified). Also VACUOUS as a Prop: WholeZkVMEndToEndClaim's conclusion (∃ validTrace, vmExecutionValid publicInput validTrace) is directly witnessed by its own hypotheses (trace, A.vmExecutionValid publicInput trace), so any degenerate A satisfies it. Self-describes honestly as 'a Prop-level checklist, not a proved zkVM theorem'. Either keep as prose-only doc (drop the Prop) or strengthen the conclusion so it is not implied by a single hypothesis.
### [PROVEN] r1csResidualAt (+ zeroCheckVirtualPolynomial_eval_boolPoint, relation_iff_zeroCheck_vanishes)
- loc: `ArkLib/ProofSystem/Spartan/Basic.lean:700`
- Ledger regex false positive: 'residual' = the R1CS row residual (A𝕫·B𝕫−C𝕫)(w), a math object. Theorems about it fully proven; Basic.olean built.
### [PROVEN] r1csResidual / zeroCheckVirtualPolynomial_eq_mle'_r1csResidual
- loc: `ArkLib/ProofSystem/Spartan/R1CSMleEquivalence.lean:201,235`
- Same false-positive family: r1csResidual is the row-residual function; r1cs_relation_iff_mle'_residual_zero and the MLE' identification are proven; R1CSMleEquivalence.olean built.
### [PROVEN] composedCompletenessResidual_of_leaves (8-leaf assembly)
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:759`
- 7-seam keystone fold over composedPIOP_Rc (2 challenge + 4 message + 1 empty seams) reducing composed PC to the 8 leaf PCs. ComposedCompleteness.olean built; axiom checks in-file.
### [PROVEN] composedCompletenessResidual_of_five_leaves
- loc: `ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:807`
- Sharpening: firstMessage (SendSingleWitness.oracleReduction_completeness) + both sum-checks (firstSumcheck/secondSumcheck_perfectCompleteness_bridgeFree, FirstSumcheckBridgeFree.lean:102 / SecondSumcheckBridgeFree.lean) discharged in-module; 5 leaves remain as hypotheses. Built.
### [PROVEN] composedRbrKnowledgeSoundnessResidual_of_leaves (+ composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves)
- loc: `ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:626`
- Proven CONDITIONAL assembly (olean built): folds the 7 seams via append_rbrKnowledgeSoundness keystones with folded error composedRbrError. The 7 verifier-determinism witnesses (firstMessage/firstChallenge/sendEvalClaim/linearCombination/..._toVerifier_pure) are proven in-file. Open inputs = the 8 per-phase rbr-KS leaves (h1..h8) + 2 hSeamZero residuals — see separate items.
### [PROVEN] composedPIOPResidual_holds_proof / composedPIOPWithClaimResidual_holds_proof
- loc: `ArkLib/ProofSystem/Spartan/Composition.lean:477,482`
- Typed-existence residuals discharged by the concrete assembled reductions composedPIOP_Rc / composedPIOPWithClaim_Rc (real 8/9-fold OracleReduction.append terms that type-check; Composition.olean built). Note the underlying Props are weak (Nonempty of the reduction type) — content is the assembly itself, which is genuine.
### [PROVEN] Bridge.StraightlineOfRewinding (ToyProblem hBridge, protocol62_knowledgeSound/_rbrKnowledgeSound)
- loc: `ArkLib/ProofSystem/ToyProblem/Spec/General.lean:300,1139ff`
- Discharged in-tree: theorem Bridge.straightlineOfRewinding_holds, ArkLib/ToMathlib/StraightlineRewindingBridge.lean:141 (grep-verified theorem exists; module olean built). Consumers taking hBridge can be fed the proof.
### [PROVEN] Plonk (#115): plonkCheckVerifier_{rbrSoundness,soundness,knowledgeSoundness,rbrKnowledgeSoundness} + gate/perm chain
- loc: `ArkLib/ProofSystem/Plonk/Composition.lean:300-659, Basic.lean, PermutationCheck.lean`
- No residual-named decls, no Prop-classes, no sorry tokens; all Plonk oleans built. Consistent with the #115 genuine closure (13 headline theorems axiom-clean). No action.
### [PROVEN] BCS: transparentBCS_perfectCompleteness / transparentBCS_soundness + ErrorAccounting suite
- loc: `ArkLib/ProofSystem/BCS/TransparentEndToEnd.lean:512,561; ErrorAccounting.lean`
- #62 end-to-end instance: both headline theorems exist (grep-verified), modules olean-built, honest hypotheses (hInit/hImplSupp/himplSP/himplNF/himplVB are standard honest-impl side conditions, also consumed identically elsewhere). ErrorAccounting is pure proven arithmetic/union-bound algebra. No action.
### [PROVEN] Component / ConstraintSystem / CommitmentScheme sweep
- loc: `ArkLib/ProofSystem/Component/**, ArkLib/ProofSystem/ConstraintSystem/**, ArkLib/CommitmentScheme/**`
- Zero residual-named decls, zero Prop-classes-without-instances, zero sorry/axiom tokens; every module has a built olean. KZG security theorems are conditional on standard named hardness GAMES (tSDH/ARSDH experiments, HardnessAssumptions.lean) — the correct cryptographic pattern, not proof debt. Transparent.lean perfectCorrectness proven. No action.
- papers: CGKY25 (KZG games)

**Pass-throughs found:**
- Spartan.Spec.spartan_rbr_knowledge_soundness — ArkLib/ProofSystem/Spartan/SpartanRBRProof.lean:41 (hypothesis hks IS the conclusion's defeq unfolding; honest, self-documented converter)
- Spartan.Spec.spartan_rbr_knowledge_soundness_with_claim — ArkLib/ProofSystem/Spartan/SpartanRBRWithClaimProof.lean:36 (same shape)
- spartan_rbr_knowledge_soundness_checkpoint — ArkLib/ToMathlib/SpartanRBRProof.lean:36 (DUPLICATE of the Spartan one, 'Master Cryptographer' swarm artifact, both imported by ArkLib.lean — deletion candidate)
- SpartanBricks converters consumed by scope: composedCompletenessResidual_of_perfectCompleteness (:= hc, ToMathlib/SpartanBricks.lean:1502), composedCompletenessWithClaimResidual_of_perfectCompleteness (:1515), composedRbrKnowledgeSoundnessResidual_of_rbrKnowledgeSoundness (:= hks, :1534), composedRbrKnowledgeSoundnessWithClaimResidual_of_rbrKnowledgeSoundness (:1549) — all literal := h; honestly labelled as converters; the former fake 'headline' duplicates were already retired per the in-file 2026-06-10 audit note
- ZkVMBoundary.WholeZkVMEndToEndClaim — ArkLib/ProofSystem/ZkVMBoundary.lean:~85: conclusion (∃ validTrace, vmExecutionValid) is a sub-formula of its own hypothesis list — vacuous implication

**Laundering/vacuity findings:** 1) SpartanBricks.lean:1574-1577 docstring states 'Perfect completeness (PROVEN, no leaf hypotheses): Bricks.composedCompletenessResidual_proven_114c' — but ComposedCompletenessProven.lean CANNOT COMPILE at HEAD (no olean; imports FirstChallengeComplete.lean which lake env lean shows has 3 hard errors: unknown identifier ofPFunctor_toPFunctor:131, ambiguous map_pure:142, failed rewrite:152). The theorem text exists (not deletion-laundering) but 'PROVEN' is unverifiable until the bit-rot repair; the claim should say 'assembled, module under repair'. 2) Seven Spartan modules are silently unbuildable while still imported by ArkLib.lean (FirstChallengeComplete, FirstChallengeLeaf, PhaseCompletenessLeaves, ComposedCompletenessFinal, ComposedCompletenessProven, ComposedCompletenessTwoLeaves [own universe-metavariable error, verified], ComposedCompletenessWithClaimFinal) — so 'zero sorry' is technically true but the root ArkLib target cannot build; in-file docstrings DO acknowledge the breakage (ComposedCompleteness.lean:42,800). 3) ArkLib.lean imports BOTH PhaseCompletenessLeaves (:1343) and ComposedCompletenessLeaves (:1321), which declare the same names (Spartan.Spec.sendEvalClaimRelOut, Spartan.Spec.linearCombinationRelOut — verified same namespace) — a duplicate-declaration import clash acknowledged in ComposedCompletenessProven.lean's docstring but never fixed in ArkLib.lean; PhaseCompletenessLeaves' only unique content (firstMessage_perfectCompleteness) is unused — delete or rename. 4) WholeZkVMResidual is vacuously satisfiable (see passThroughs) — by-design checklist, but the Prop should not be mistaken for an obligation. 5) No deletion-laundering found in scope: every docstring-cited theorem name in Spartan/Sumcheck/Plonk/BCS/ToyProblem was grep-confirmed to exist in source.

## Whole-tree structural audit of ArkLib proof debt: (1) all pass-through theorems under hResidual/hApp

### [OPEN-RESEARCH] Binius/FRIBinius full-protocol apexes (fullOracleReduction_perfectCompleteness, fullOracleVerifier_rbrKnowledgeSoundness ×2 files; coreInteraction ×2)
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:117,149; BinaryBasefold/CoreInteractionPhase.lean:1137,1174; FRIBinius/General.lean:191,237`
- NOT discharged — all six are verbatim pass-throughs (exact h<hyp> with hypothesis = conclusion; hInit decorative). The DP24 §5.2 eq.(43) concrete error is defined but the security content is entirely assumption-level pending the 13 residual classes. Classified open in-tree (provable from DP24 with the classes closed); honest state = keep conditional, docs must not claim Binius security proven.
- papers: DP24 §5.2 eq.(43)
### [OPEN-RESEARCH] MLIOPCS security-field structure + bbfMLIOPCS concrete instance
- loc: `ArkLib/ProofSystem/RingSwitching/Prelude.lean:266 (fields perfectCompleteness:279, rbrKnowledgeSoundness:290); instance ArkLib/ProofSystem/Binius/BBFSmallFieldIOPCS.lean:679`
- MLIOPCS carries perfectCompleteness + rbrKnowledgeSoundness as FREE structure fields. The one concrete instance (bbfMLIOPCS:679) discharges them only by routing through the BinaryBasefold pass-throughs — i.e. through undischarged assumptions — AND the source as written looks non-elaborating against the current tree (BBFSmallFieldIOPCS.lean:478 supplies only hInit to a 2-hypothesis pass-through; liftContext_perfectCompleteness post-2026-06-04 repair needs hStmt+[LiftContextCoherent], not supplied; no .olean exists for this module or BinaryBasefold/General). Treat MLIOPCS fields as assumptions; the RingSwitching results conditional on them remain honest.
### [OPEN-RESEARCH] RingSwitching SumcheckPhase coreInteraction pass-throughs
- loc: `ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1834,1879`
- Verbatim pass-throughs (exact hAppendPerfectCompleteness / hAppendRbrKnowledgeSoundness; hRounds decorative in the first). Load-bearing only as named seams for the proven EndToEnd assembly above — keep, but they prove nothing themselves.
### [OPEN-RESEARCH] STIR rbr soundness residuals (stirCheckingRbrSoundnessResidual, stirMultiRoundRbrSoundnessResidual)
- loc: `ArkLib/ProofSystem/Stir/CheckingVerifier.lean:955; MultiRoundAssembly.lean:222`
- Honestly open and documented so: MultiRoundAssembly.lean:40 says the shell residual is 'open-and-likely-false in regimes' — keep named, never discharge as stated; the checking-verifier residual is the honest target, gated on Johnson correlated agreement (in-tree: the StrictCoeffPolysResidual cone). Consumers are uniformly conditional (hSound/hSecure hypotheses). Paper math exists (BCIKS20+STIR) but the in-tree CA gate is the same γ-root wall as WHIR.
- papers: ACFY24 STIR §5; BCIKS20
### [OPEN-RESEARCH] whir_rbr_soundness
- loc: `ArkLib/ProofSystem/Whir/RBRSoundness.lean (statement-only)`
- Statement-only Prop, gated on mca_johnson_bound_CONJECTURE per FoldRound.lean:38; #113 audit stands (wrappers are existential plumbing). Cannot be closed until the CA gate lands; keep conditional.
### [OPEN-RESEARCH] #232 GrandChallenge MCA conjecture web (~100 decls: mcaConjecture, epsMCAgsPrizeUniformConjecture, epsMCAgsPrizeUniversalConjecture, UniversalGSListMassBound, UniformPolyListSizeConjecture + all *_of_uniformConjecture / *_of_ignoredSource_mcaConjecture plumbing in GrandChallenge141*/GrandChallenges*/Lattice*)
- loc: `ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge*.lean, GrandChallengesLattice*`
- This is the Proximity Prize surface (delta* pin in (1-sqrt(rho),1-rho)): CANNOT be closed — maintainer-designated keep-open tracker. Every theorem in the family is verified conditional plumbing over the named conjectures. Refutations proven where the surface is false: not_uniformEpsMCAgsPrizeBoundConjecture (MCAGSPrizeRefutation.lean:102 + keep copy), not_mcaConjecture_of_cs25BreakdownBelowBound (MCAConjectureRefutation.lean:62). Honest end state achieved: named Props, conditional consumers.
### [OPEN-RESEARCH] BCIKS20 StrictCoeffPolysResidual cone (~30 decls: StrictCoeffPolysResidual(+Large/Canonical), CurveCommonAgreementResidual, RSCurveListSizeResidual, producers in LocalSeriesProducer/StrictCoeffProducer/CurveHensel*/Keystone*/Offcentre*/Faithful*)
- loc: `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:2505-2647 + producer files`
- Central open gate of the BCIKS20 formalization: every producer (of_betaRec, of_curveHenselDatum, of_gsCurveInput, of_localSeriesDatumOn, of_section5Data*, of_faithful_frontier, of_rawGSCargo) is a proven conditional brick; the apex residual itself is undischarged — the genuine gap is the gamma-is-a-root Hensel/series core. Paper math proven (BCIKS20) but multiple in-tree attacks failed; treat as formalization-open. Vacuous-regime discharges (CoeffExtractionVacuous of_one_le_mul/of_card_le/_e7) are honest but parameter-vacuous.
- papers: BCIKS20 §5-7
### [OPEN-RESEARCH] Claim57Residuals / Claim57ResidualsDescended classes
- loc: `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:1815; DescendedRset.lean:410`
- Prop-classes with NO unconditional instances; all producers (ofInTree, ofInTree2, ofDescended, ofGraphExtractionHypotheses, claim57Residuals_of_johnson/_of_natCeil/_of_gsInterpolant) take genuine named hypotheses (hx0 separability, hsep). Descended route discharges per-member discr_y≠0 but end-to-end extraction is gated on pg_RsetDescended = pg_Rset, false in the inseparable case. Same γ-root wall; keep conditional.
- papers: BCIKS20 Claim 5.7
### [OPEN-RESEARCH] GKL24 first-moment residual family (~12 decls) + randomLinearLambdaLowerFirstMomentResidual + AGL24 randomRSListDecodingFirstMomentResidual + diffStackMCAResidualBelowUDR
- loc: `ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean:1045-1503, GKL24PetalWitnessCover.lean; ListDecoding/Bounds/RandomAndReedSolomon.lean:142; ToMathlib/{AGL24RandomRSProof.lean:78,L46DiffStackRS.lean,L46GSLowerBound.lean}`
- inTree card discharges proven (GKL24FirstMomentResidual_inTree_card/_two_delta/_delta_add_one); the witness-cover residuals (MaxCorr/Petal/MaxDomain) and the first-moment apexes are the average-to-worst-case-past-Johnson surface of #232 — open. Conditional converters between cover notions all proven. NOTE: ledger entries at ListDecoding/Bounds.lean:1461+ are STALE — that file is now a 146-line import hub; the decls live only in Bounds/RandomAndReedSolomon.lean (no duplicate).
### [OPEN-RESEARCH] Quarantine candidate MCA-bound Props (~12 files: candidate_*_mca_bound, HasExtrapolativeBound, slice_rank_capacity_bound, smooth_subgroup_kernel_bound, hyp_HasseWeil_agreement_bound)
- loc: `ArkLib/Data/CodingTheory/Quarantine/Candidate*.lean`
- Deliberately quarantined #232 attack candidates — statement-only Props with no discharge by design, isolated from the main tree. Correct honest state; do not promote without proof.
### [OPEN-RESEARCH] PerRoundProximityGap (duplicate defs) + RSPhases BatchingConsistencyResidual
- loc: `ArkLib/ProofSystem/Whir/KeystoneReduction.lean:52 ≡ ArkLib/ProofSystem/Stir/ErrorAccumulation.lean:307; ArkLib/ToMathlib/RSPhases.lean:128`
- PerRoundProximityGap is defined twice (WHIR + STIR forms) — consolidation candidate; both discharged only conditionally from the faithful front door (CurveFamilyRoundConsumers.lean:144-209), which is itself gated on the StrictCoeffPolysResidual cone. BatchingConsistencyResidual has only the _sum brick. All sit on the same BCIKS gate.
### [OPEN-RESEARCH] WholeZkVMResidual
- loc: `ArkLib/ProofSystem/ZkVMBoundary.lean:109`
- Self-described 'Prop-level checklist, not a proved zkVM theorem'; no consumers. Honest boundary template — keep named or delete; nothing depends on it.
### [OPEN-RESEARCH] Logup BridgeAndAppendResiduals + Errors diffStack consumers + Issue141Kernels UniformPolyListSizeConjecture
- loc: `ArkLib/ProofSystem/Logup/Security/BridgeAndAppendResiduals.lean:237; ProximityGap/Errors.lean:1597; Issue141Kernels.lean:51`
- of_binary bridge PROVEN (axiom-checked in-file); diffStackMCAResidualBelowUDR + UniformPolyListSizeConjecture are #232 lower-bound-side named surfaces — open, conditional consumers only.
### [PROVABLE (M)] appendSoundnessResidual — general challenge-at-seam case
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:957,1142`
- msg-seam proven (append_soundness_msg'); no theorem append_soundness_challenge exists. Route: replay AppendSoundnessMsgProof's canonical seam chain with evalDist_run'_challengeSeam_left/right (AppendSoundnessSeamTransfer.lean, already proven) replacing the msg bridges; the W1/W2 union-bound machinery (probComp_seam_swap_union_le) is seam-type-agnostic.
### [PROVABLE (L)] appendKnowledgeSoundnessResidual (straightline KS append, both layers)
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:984,1162`
- Genuinely open: needs malicious-prover seam decomposition + extractor query-log routing (proveQueryLog.fst/verifyQueryLog) over the proven Extractor.Straightline.append. Soundness-side union bound already exists; the extractor leg is new. No discharge theorem found.
### [PROVABLE (L)] appendRbrSoundnessPhase2Residual
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKeystone.lean:282`
- Phase 1 + all bricks proven (AppendRbrKeystone, AppendRbrSoundnessPhase2Proof.lean has StateFunction.doom/appendDoomed_toFun bricks); remaining = Prover.snd msg-seam factoring at the phase boundary. No *_holds exists.
### [PROVABLE (L)] DuplexSponge security residual family (KeyLemmaResidual, Lemma5_8EagerBirthdayResidual, Lemma5_12/14/16HonestResidual, SimulatedProver*/D2s/D2f budget residuals, Hyb01-34StepResidual, duplexSponge runCollapse ×2) — 13 decls
- loc: `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/{KeyLemma.lean:241,KeyLemmaFoundations.lean:641-1013,KeyLemmaHybrids.lean:619-681,BirthdayBound.lean:417,Completeness.lean:200-212}`
- All consumed as named Prop hypotheses; none discharged. Game/budget/numeric scaffolding proven in-tree. CAVEAT documented in KeyLemmaFoundations.lean:185 — in-tree KeyLemmaResidual claims MORE than the paper's Claims 5.21-5.24 prove; statement repair needed before discharge. Honest end state until then: keep named, consumers conditional.
- papers: CO25 duplex-sponge Fiat-Shamir security (Lemmas 5.1, 5.8, 5.12, 5.14, 5.16)
### [PROVABLE (L)] Binius 13 assumption-classes (FoldPreservesBBFCodeMembershipResidual, FoldMatrixDetNeZeroResidual, FinalSumcheckStepLogicCompleteResidual, ExtractMLPCorrectnessResidual, Prop4212Case1/2, PreTensorCombine*, FoldEqMultilinearPreTensorStep1, Prop421Case1/2Fiberwise, PreviousSuffixFiberAlignment)
- loc: `ArkLib/ProofSystem/Binius/BinaryBasefold/{Code.lean:992,Prelude.lean:1968,ReductionLogic.lean:1363,Relations.lean:207,Soundness/*.lean}`
- Verified: ZERO instances in-tree for all 13 (grep instance.*<class> = 0 each). Pure free-assumption classes; every BinaryBasefold soundness theorem is conditional on them. Math is the published DP24 BaseFold/Binius soundness steps (Prop 4.21, 4.2.12, fold-code membership, tensor-combine multilinearity).
- papers: DP24 (Diamond-Posen, ePrint 2023/1784) §4; Prop 4.21-4.24
### [PROVABLE (L)] FRI completeness residuals (queryRound/foldPhase/reductionPerfectCompletenessResidual + ToMathlib foldRound/finalFoldRound)
- loc: `ArkLib/ProofSystem/Fri/Spec/Completeness.lean:29,52,84; ArkLib/ToMathlib/FriComplete.lean:106,131`
- NONE discharged — every consumer takes them as hypotheses (hRounds/hFinal/hResidual); FriCompleteCompose 'Brick C' is a vacuous pass-through. Route: per-round fold consistency (fold of close codeword stays close + verifier check passes on honest fold) is standard FRI completeness; the run-shape unrolling infra (generic unroll keeping runToRound opaque) already exists from the STIR #301 work.
- papers: BBHR18 (FRI, ICALP) §4 completeness
### [PROVABLE (M)] Logup OuterSoundnessResidual (malicious-prover outer) + LogupSoundnessFull/UncondResidual apexes
- loc: `ArkLib/ProofSystem/Logup/Security/SubPhaseSplit.lean:70; LogupSoundnessClose.lean:170; LogupSoundnessUncond.lean:241; OuterSoundnessReal.lean:466`
- Open leg: outer soundness vs malicious prover — reduced to run-unfolding via outerSoundnessResidual_real_of_runUnfolding (OuterSoundnessReal.lean:466) and to the marginal bridge via OuterRunSamplesChallenge.lean:185; per #13 memory the malicious-prover outer template exists. Apex defs LogupSoundnessFull/UncondResidual remain named conditionals consumed as (h : ...).
### [PROVABLE (L)] Spartan composedRbrKnowledgeSoundnessResidual
- loc: `ArkLib/ToMathlib/SpartanBricks.lean:1234 (comment :1250 'no proof yet'); ComposedRbrKnowledgeSoundness.lean:626`
- Explicitly open in-file. Only conditional converters exist (of_leaves, of_rbrKnowledgeSoundness, WithClaim valueRel equivalences); SpartanRBRProof.lean checkpoint is a self-documented hResidual→hResidual pass-through. Route: 8-fold assembly of the leaf rbr-KS theorems through the (now subsingleton-proven) append rbr-KS keystone; blocked on general-σ only if a stateful impl is required.
### [PROVABLE (L)] WHIR mca_johnson_bound_CONJECTURE
- loc: `ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:319`
- Paper-proven math (BCIKS20 Thm 1.2 Johnson-regime correlated agreement) but the in-tree route is gated on the StrictCoeffPolysResidual/Hensel γ-is-a-root core, which has resisted sustained effort (RationalFunctions Hensel dev). Conditional bricks proven: _smallField, _holds_of_rawGSCargo, the 13 pair-reduction theorems (MCAConjecturePairReduction). Formalization-hard; keep conditional consumers until the γ-root core lands.
- papers: BCIKS20 (ePrint 2020/654) Thm 1.2, §5-7
### [PROVABLE (L)] Hab25JohnsonResiduals bundle
- loc: `ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean:329 + NumericBridge`
- Structure-bundle with conditional producers (ofAlgebraicData, numeric covers); frontier = hImprove weld + Z-degree budget + S11 from the Hab25 development (S5-global squarefree-WLOG already landed). Genuine open formalization with a mapped route.
- papers: Hab25 (Johnson-regime CA improvement) §5, §11
### [DEAD] VectorIOP.IsSecureWithGap / VectorIOR.IsSecure ×2
- loc: `ArkLib/OracleReduction/VectorIOR.lean:131,157,175`
- IsSecure (both) : zero instances, zero consumers — dead interface, deletion candidates. IsSecureWithGap: zero instances, consumed only as free hypothesis (hSecure) by STIR MultiRoundAssembly:265,352 — assumption-class; keep only if STIR assembly is kept, else dead.
### [DEAD] WHIR mca_capacity_bound_CONJECTURE
- loc: `ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:363`
- Mis-stated as a target: MCACapacityTrivial_keep.lean:19 proves the def trivially true (vacuous as a conjecture), and the intended up-to-capacity claim is FALSE (MCAUpToCapacityFalse refutation; CS25/KK25 counterexamples). Keep only the refutation; the CONJECTURE def is a deletion candidate after consumers are re-pointed.
### [DEAD] BoundaryCard* residual family (~35 decls incl. ToMathlib/BoundaryDischarge.lean producers)
- loc: `ArkLib/Data/CodingTheory/ProximityGap/BoundaryCard*.lean, BoundaryLatticeThresholdLeaf.lean, ArkLib/ToMathlib/BoundaryDischarge.lean`
- The residual Props are REFUTED in-tree: not_boundaryCardResidual, not_boundaryCardLatticeResidual, not_boundaryCardQuantizationResiduals, not_boundaryProbabilityResidual (BoundaryCardResidualRefutation.lean:246-274), not_boundaryCardStrictInteriorResidual (+nonSquareEndpoint), not_boundaryCardResidual_affineLine. Dead as proof obligations; the conditional producer/equivalence lemmas over them are vacuously-satisfiable bricks kept as the refutation record. Consolidation/deletion candidate (keep the refutation theorems).
### [DEAD] GrandChallenge1BruteForce Hyp*Bound Props
- loc: `ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge1BruteForce.lean:22,52`
- Tier-1 refutations proven sorry-free in GrandChallenge1RefutationProofs.lean (Hyp3/5/6/7/8/9/10) — dead as obligations, kept as refutation record.
### [PROVEN] Append.lean named-residual dozen (reductionAppendCompleteness/PerfectCompleteness, Verifier.appendSoundness/KnowledgeSoundness/RbrSoundness/RbrKnowledgeSoundness, OracleReduction+OracleVerifier mirrors)
- loc: `ArkLib/OracleReduction/Composition/Sequential/Append.lean:901-1227`
- SPLIT FAMILY. Discharged in-tree: perfect-completeness msg seam (reductionAppendPerfectCompletenessResidual_of_message AppendPerfectCompletenessMsg.lean:392; oracle version append_perfectCompleteness_msg_proof AppendPerfectCompletenessOracle.lean:81 + AppendPerfectCompletenessProof.lean:108), non-perfect completeness msg seam (append_completeness_msg AppendSeamBridges3.lean:254, append_completeness_msg_proof AppendCompletenessNonPerfect.lean:133), challenge-seam completeness (append_completeness_msg_via_seamFactor AppendChallengeSeam.lean:210), soundness msg seam (append_soundness_msg' AppendSoundnessMsgProof.lean:230, axiom-clean). Still open within family: see separate items for challenge-seam soundness, knowledge soundness, rbr Phase-2.
### [PROVEN (L)] appendRbrKnowledgeSoundnessPhase2Residual / rbr-KS keystone
- loc: `ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeStateFunction.lean:1226 (+944)`
- PROVEN for [Subsingleton σ]: appendRbrKnowledgePhase2SeamReconcile_proof (AppendRbrKnowledgePhase2ReconcileProof.lean:64) and append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional (:349) — covers stateless impls (BCS, RingSwitching wired apex). General σ remains provable-hard (3 obstructions: msg-seam, carried-state, σ-threading).
### [PROVEN] appendRunRightResidual(+Dist) and appendToReductionResidual
- loc: `Append.lean:4112-4138; AppendRunEvalDist.lean:53-104; AppendRunEvalDistChallenge.lean:265; EmptyAppend.lean:84; AppendToVerifierKeystone.lean:148`
- All discharged: appendRunRightResidual_holds_msg (Append.lean:4138), _holds_empty (EmptyAppend.lean:84), appendRunRightResidualDist_holds_msg/_challenge, appendToReductionResidual_proof (AppendToVerifierKeystone.lean:148; iff-bridge at AppendPerfectCompletenessOracle.lean:122).
### [PROVEN] FiatShamir transfer residuals (runCollapse, soundnessTransfer, knowledgeSoundnessTransfer, statisticalHVZK, hvzk) — 36 ledger decls
- loc: `ArkLib/OracleReduction/FiatShamir/Basic.lean:303-1332 + closing files`
- All five core residuals discharged, theorems verified to exist: fiatShamir_runCollapseResidual proved in BasicCompleteness.lean:150; fiatShamir_soundnessTransferResidual_canonical (StateRestorationTransport.lean:899); fiatShamir_knowledgeSoundnessTransferResidual_canonical (:3301); fiatShamir_statisticalHVZKTransferResidual_canonical_proved (HVZKCanonicalClose.lean:79); fiatShamir_hvzkTransferResidual_canonical_proved (HVZKKernelClose.lean:1080). ZKResidualBridge iff-lemmas are honest plumbing. Matches #116 CLOSED.
### [PROVEN] RingSwitching apex completeness (fullOracleReduction_perfectCompleteness, General.lean:456) + wired rbr-KS
- loc: `ArkLib/ProofSystem/RingSwitching/General.lean:396-456; RbrKnowledgeWiringFull.lean:119`
- Completeness apex proven end-to-end (delegates to fullOracleReduction_perfectCompleteness'; per file comment all five former phase/append residual hypotheses discharged internally; survivors = NeverFail init + 2 abstract-opening msg-seam facts the abstract MLIOPCS cannot carry — structural, not debt). rbr-KS wired version proven for [Subsingleton σ] via the Phase-2 subsingleton keystone. The generic General.lean:200 rbrKS theorem remains a genuine (non-pass-through) conditional assembly via OracleVerifier.append_rbrKnowledgeSoundness.
### [PROVEN] Logup completeness residual web (~20 decls: SubPhase/Outer/Sumcheck/Append/Brick completeness residuals)
- loc: `ArkLib/ProofSystem/Logup/Security/{SubPhaseSplit,OuterCompleteness,SumcheckCompleteness*,LogupCompleteness*}.lean`
- End-to-end discharged, theorems verified to exist: logup_completeness_final (LogupCompletenessFinal.lean), sumcheckCompletenessResidual_unconditional + subPhaseCompletenessResidual_unconditional (SumcheckCompletenessUncond.lean:51,67), outerCompletenessRunResidual_proved + outer_completenessRunFactsResidual (OuterCompleteness.lean:813,831), appendCompletenessResidual_wired (LogupCompletenessWired.lean:183). Matches #13 completeness DONE.
### [PROVEN] Logup soundness residual web — SumcheckSoundnessResidual + AppendSoundnessResidual legs
- loc: `ArkLib/ProofSystem/Logup/Security/{SumcheckSoundness*,LogupSoundnessUncond.lean:117,166,Issue13Status.lean:256}`
- sumcheckSoundnessResidual discharged including the former hProj gap: sumcheckSoundnessResidual_holds (SumcheckSoundnessLift.lean:193), _holds_projClosed (SumcheckSoundnessProjClosed.lean:109), _holds_wired, issue13_sumcheckSoundnessResidual_projClosed (Issue13Status.lean:256). Append leg discharged from the proven plain msg-seam soundness (oracleAppendSoundnessResidual_of_plain / logupAppendSoundnessResidual_of_plain). Remaining conditional inputs are standard (hError sum equation, inner multi-round rbr into Set.univ, honest-impl himplSP/NF/VB) — see next item.
### [PROVEN] Sumcheck oracleReductionToReductionResidual
- loc: `ArkLib/ProofSystem/Sumcheck/Spec/OracleCompleteness.lean:54; OracleCompletenessUncond.lean:85`
- Discharged for the consuming concrete case: oracleReductionToReductionResidual_of_binary (Logup/Security/BridgeAndAppendResiduals.lean:237, with in-file #print axioms check) + _of_perRound generic reduction. Generic abbrev remains as interface — fine.
### [PROVEN] Sumcheck hSeqCompose / hRound rbr chain
- loc: `ArkLib/ProofSystem/Sumcheck/Spec/{OracleRbrSoundness.lean:113,175, SeqComposeRbrSoundness.lean:406+}`
- Genuine reduction chain, not pass-through: hRound proven (oracleVerifier_rbrKnowledgeSoundness, SingleRound.lean:1220, deg/|R| error); hSeqCompose discharged for the concrete sum-check oracle verifier in SeqComposeRbrSoundness.lean §'Discharging hSeqCompose'.
### [PROVEN] Spartan completeness/PIOP residuals (composedCompleteness, composedPIOP, WithClaim variants, r1csResidual, secondSumcheck/firstSumcheck/finalCheck/r1csMleEncoding residuals)
- loc: `ArkLib/ProofSystem/Spartan/* + ArkLib/ToMathlib/SpartanBricks.lean:474-1213`
- Discharged, theorems verified to exist: composedCompletenessResidual_proven (ComposedCompletenessFinal.lean:88) + _proven_114c, composedCompletenessWithClaimResidual_proven, composedPIOPResidual_holds_proof + WithClaim (Composition.lean:477,482), secondSumcheckTerminalEndpointResidual_holds, finalCheckWithClaimValueRelResidual_holds, secondSumcheck/firstSumcheckResidual_holds, r1csMleEncodingResidual_holds (SpartanBricks). Remaining iff/converter lemmas are honest plumbing. Matches #114/#115 closures.
### [PROVEN] STIR round completeness (stirRoundReduction_completeness)
- loc: `ArkLib/ProofSystem/Stir/RoundProtocol.lean:196`
- Discharged: stirRoundReduction_completeness_proved (RoundCompleteness.lean:200, with #print axioms) + any-error monotone variant.
### [PROVEN] Security/Basic + lens Prop-class interfaces (IsComplete, IsPerfectComplete, IsSound, IsKnowledgeSound, Extractor.Lens.IsKnowledgeSound, Extractor.Straightline.IsMonotone, AppendCoherent, Codec.IsLawful, Serialize.IsInjective)
- loc: `ArkLib/OracleReduction/Security/Basic.lean:158-412; LiftContext/Lens.lean:467; Append.lean:331`
- Legitimate interfaces WITH concrete in-tree instances: instTestLensComplete (LiftContext/Reduction.lean:1791), canonical pullback lens-soundness instance (Spartan/SumcheckPhaseRbr.lean:101), Extractor.Lens.IsKnowledgeSound instances (Sumcheck SingleRound:1726, SeqComposeRbrSoundness:452, FRIBinius CoreInteractionPhase:346), AppendCoherent instances per protocol (RingSwitching SumcheckPhase:1816, Fri SingleRound). Not free assumptions.
### [PROVEN] FaaDiBrunoSuccSumZeroResidual + βHensel weight residuals
- loc: `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:1598-2690; P2*.lean`
- Mixed-resolved: βHenselSuccTermStructuredWeightResidual_holds PROVEN (HenselNumerator.lean:2690, verified exists); FaaDiBrunoSuccSumZeroResidual REFUTED in the constant/non-monic regime (faaDiBrunoSuccSumZeroResidual_false, P2OrderZeroRefutationWitness.lean:168, + 3 case refutations) — so that residual must not be assumed globally; remaining P2 bridges (of_leadingCoeff_one, of_WfreeMatch, of_partitionMatch) are conditional bricks in the monic case.
### [PROVEN] GK16Lemma12HardResidual
- loc: `ArkLib/Data/CodingTheory/ProximityGap/GK16Lemma12.lean:400`
- gk16Lemma12HardResidual_holds (GK16Lemma12.lean:440), verified exists.
### [PROVEN] DeepHoleProbResidual (CS25)
- loc: `ArkLib/ToMathlib/CS25DeepHoleFinish.lean:262`
- deepHoleProbResidual_holds (CS25JointFar.lean:203) + _of_jointFar bridge; consumed by hDeepHole_of_probResidual.
### [PROVEN] MCACapacityTrivial_keep + MCAGSRefutationCore_keep
- loc: `ArkLib/MCACapacityTrivial_keep.lean:19; ArkLib/MCAGSRefutationCore_keep.lean:101`
- Keep-file witnesses: triviality of the mis-stated capacity CONJECTURE def and the refutation of uniformEpsMCAgsPrizeBoundConjecture (duplicate of MCAGSPrizeRefutation.lean:102 — intentional keep copy). Both verified to exist.

**Pass-throughs found:**
- Reduction.reduction_append_completeness — Append.lean:909 (:= hResidual; h₁,h₂ decorative)
- Reduction.reduction_append_perfectCompleteness — Append.lean:927
- Verifier.append_soundness — Append.lean:964
- Verifier.append_knowledgeSoundness — Append.lean:992
- Verifier.append_rbrSoundness — Append.lean:1018
- Verifier.append_rbrKnowledgeSoundness — Append.lean:1057
- OracleReduction.append_completeness — Append.lean:1104
- OracleReduction.append_perfectCompleteness — Append.lean:1124
- OracleVerifier.append_soundness — Append.lean:1151
- OracleVerifier.append_knowledgeSoundness — Append.lean:1171
- OracleVerifier.append_rbrSoundness — Append.lean:1193
- OracleVerifier.append_rbrKnowledgeSoundness — Append.lean:1216
- Fri.Spec.reduction_perfectCompleteness_of_phases — ToMathlib/FriCompleteCompose.lean:72-101 (exact hResidual; hFold/hQuery/AppendCoherent unused — laundering-adjacent)
- Fri.Spec.Completeness.queryRound_perfectCompleteness — ProofSystem/Fri/Spec/Completeness.lean:39-49
- Fri.Spec.Completeness.foldPhase_perfectCompleteness — ProofSystem/Fri/Spec/Completeness.lean:~70-80
- Fri.Spec.Completeness.reduction_perfectCompleteness — ProofSystem/Fri/Spec/Completeness.lean:118-145 (unfold residual + chain of pass-throughs)
- Binius.BinaryBasefold.CoreInteraction.coreInteractionOracleReduction_perfectCompleteness — BinaryBasefold/CoreInteractionPhase.lean:1137-1164 (hInit decorative)
- Binius.BinaryBasefold.CoreInteraction.coreInteractionOracleVerifier_rbrKnowledgeSoundness — BinaryBasefold/CoreInteractionPhase.lean:1174-1188
- Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness — BinaryBasefold/General.lean:117-134 (hInit decorative)
- Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness — BinaryBasefold/General.lean:149-165
- Binius.FRIBinius fullOracleReduction_perfectCompleteness — FRIBinius/General.lean:191
- Binius.FRIBinius fullOracleVerifier_rbrKnowledgeSoundness — FRIBinius/General.lean:237-255 (:= hAppendRbrKnowledgeSoundness)
- RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness — RingSwitching/SumcheckPhase.lean:1834-1862 (hRounds decorative)
- RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness — RingSwitching/SumcheckPhase.lean:1879-1906
- SpartanRBR.spartan_rbr_knowledge_soundness_checkpoint — ToMathlib/SpartanRBRProof.lean:35-52 (SELF-DOCUMENTED honest hResidual→hResidual checkpoint)
- NOT pass-throughs (verified genuine): Sequential/General.lean:466,506 and SeqComposeVerifierBricks.lean:54,84 (n-ary induction applying binary hAppend per step); RingSwitching/General.lean:124-168,200-266 (real append assembly feeding hResidual into append_* combinators); BatchingPhase.lean:560-568 (residual consumer); DeBruijnTwoPrime hFull uses (math, applied to indices)

**Laundering/vacuity findings:** 1) AppendSeamBridges.lean (header, lines 32-46) claims four theorems "proven here (no sorry)" — appendStage1Bridge, appendStage2Bridge, append_game_neverFail, append_completeness_msg — but the file contains NONE of them (only appendStage₁_run_eq_liftM:173 and seam-lift helpers). The four theorems DO exist in AppendSeamBridges3.lean:64,97,143,254, so content is real but the docstring is location-laundered; also appendStage₁_run_eq_liftM is duplicated (Bridges:173 vs Bridges2:145). 2) FriCompleteCompose.lean:72 "Brick C — binary append composition of the FRI phases": docstring advertises composition via the proven append_perfectCompleteness, but the proof is `exact hResidual` and the hFold/hQuery/AppendCoherent arguments are entirely unused — a decorated pass-through masquerading as a composition brick. 3) BBFSmallFieldIOPCS.lean: bbfMLIOPCS (:679) is presented as the concrete MLIOPCS instance discharging the security fields, but its completeness leg (:478) calls the BinaryBasefold pass-through with only hInit (the pass-through requires the conclusion itself as a second hypothesis) and calls OracleReduction.liftContext_perfectCompleteness without the post-2026-06-04 hStmt/[LiftContextCoherent] arguments; no .olean exists for this module or for BinaryBasefold/General (1696 oleans present, these absent). Strong suspicion the file does not elaborate against the current tree — the Binius security apexes should be treated as still assumption-level. 4) mca_capacity_bound_CONJECTURE (Whir/MutualCorrAgreement.lean:363) is vacuous as stated — MCACapacityTrivial_keep proves it trivially true while the intended claim is refuted (MCAUpToCapacityFalse); the def survives as a misleading name. 5) PromotedHypothesesA.lean declares a lawless local `class Field` (5 operations, zero axioms) shadowing Mathlib's Field, and is imported by ArkLib.lean:749 — its hypothesis proofs/refutations quantify over a bare signature, a vacuity hazard; quarantine/rename recommended. 6) KeyLemmaResidual (DuplexSponge) is documented in-file (KeyLemmaFoundations.lean:185) as claiming MORE than CO25 Claims 5.21-5.24 can prove — an honest statement-bug note, but the residual is undischargeable as stated. 7) AUDIT_LEDGER.md is stale in places: ListDecoding/Bounds.lean:1461+ entries point at decls that moved to Bounds/RandomAndReedSolomon.lean (Bounds.lean is now a 146-line hub). 8) Historical marginalBridge deletion-laundering is REPAIRED: theorem marginalBridge_holds exists (Logup/Security/MarginalBridgeProof.lean:374) and is consumed by three files. 9) Cosmetic-assurance pattern: `#print axioms` applied to Prop DEFS (e.g. LogupSoundnessClose.lean:201 on LogupSoundnessFullResidual) proves nothing about discharge — harmless but should not be read as verification.
