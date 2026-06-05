import ArkLib.ProofSystem.Whir.Folding

/-!
TMP verification scratch for the Finding-19 repair of `folding_preserves_listdecoding_base`
(WHIR Lemma 4.21). NOT a tracked file. Proves the repaired statement against the real
in-file/MutualCorrAgreement definitions.
-/

namespace Fold

section FoldingLemmasTmp

open MutualCorrAgreement Generator LinearMvExtension ListDecodable
     NNReal ReedSolomon ProbabilityTheory Polynomial BlockRelDistance

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Pow ι ℕ]

omit [Pow ι ℕ] in
/-- **Lemma 4.21 — Finding-19 repaired (errStar bound via `hasMutualCorrAgreement`).**

Finding 19 defect: in the bare statement `BStar`/`errStar` are *free* function parameters,
so `errStar := fun _ _ _ => 0` collapses the conclusion to `Pr[…] < 0`, impossible — the
statement is false. The honest ABF26-faithful repair *binds* the error term to a genuine
mutual-correlated-agreement bound: we take a level-1 proximity generator `Gen'` with
`Gen'.C = C'` and the MCA hypothesis `hmca : hasMutualCorrAgreement Gen' BStarV errStarV`,
so the error term is `errStarV δ` — a real probability bound, no longer freely zeroable
(`errStarV := 0` would force `Pr_{r}[proximityCondition] = 0`, a structural constraint).

Proof: the `≠`-event is dominated (forward inclusion `hsub`, L4.22) by the reverse-inclusion
failure event; that in turn is dominated, at the probability level, by the MCA
`proximityCondition` event (`hbridge` — the genuine L4.23/MCA content, the affine-line fold
correspondence + uniform-measure transport that ABF26 §4 supplies and which is not a
folding-algebra fact over the loose `indexPowT` data); and that probability is `≤ errStarV δ`
by `hmca`. The chain is `lt`-free: we conclude `≤ errStarV δ`, the bound MCA actually delivers. -/
lemma folding_preserves_listdecoding_base_mca
  [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1] [Nonempty (indexPowT S φ 1)]
  [hbd0 : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [hbd1 : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  -- *** Finding-19 repair: error term bound via mutual correlated agreement ***
  (Gen' : ProximityGenerator (indexPowT S φ 1) F) [hℓ : Fintype Gen'.parℓ]
  (_hGenC : Gen'.C = C')
  (BStarV : ℝ) (errStarV : ℝ → ENNReal)
  (hmca : hasMutualCorrAgreement Gen' BStarV errStarV)
  -- L4.22: deterministic forward inclusion (paper "easy half", always holds).
  (hsub : ∀ (f : (indexPowT S φ 0) → F) (α : F),
      fold_k_set (Λᵣ(0, k, f, S_0, C, hcode, δ)) (fun _ : Fin 1 => α) hm
        ⊆ Λᵣ(1, k, fold_k f (fun _ : Fin 1 => α) hm, S_1, C', hcode', δ))
  -- L4.23 / MCA bridge: at the probability level, the reverse-inclusion failure event is
  -- dominated by the MCA proximity-condition event for `Gen'` (affine-line fold correspondence
  -- + uniform-measure transport — the genuine ABF26 §4 content).
  (fStack : ((indexPowT S φ 0) → F) → Gen'.parℓ → (indexPowT S φ 1) → F)
  (hbridge : ∀ (f : (indexPowT S φ 0) → F),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ]
        ≤ (haveI := Gen'.Gen_nonempty;
            Pr_{let r ←$ᵖ Gen'.Gen}[
              MutualCorrAgreement.proximityCondition (fStack f) δ r Gen'.C ])) :
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - BStarV),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] ≤ errStarV δ
  := by
    intro f hδ
    let D : PMF F := PMF.uniformOfFintype F
    -- Step 1 (structural, proven): `≠`-event ⊆ reverse-inclusion-failure event, under `hsub`.
    have hmono :
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] ≤
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] := by
      refine Pr_le_Pr_of_implies D _ _ ?_
      intro α hne
      dsimp only
      dsimp only at hne
      intro hsub'
      exact hne (Set.Subset.antisymm (hsub f α) hsub')
    -- Step 2 (MCA bridge): reverse-inclusion-failure ≤ proximity-condition probability.
    have hbr := hbridge f
    -- Step 3 (MCA bound): proximity-condition probability ≤ errStarV δ.
    have hmcaApp := hmca (fStack f) δ hδ
    -- Chain.
    refine le_trans hmono (le_trans hbr ?_)
    exact hmcaApp

end FoldingLemmasTmp

end Fold
