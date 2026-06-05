/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Combinatorial
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Toy problem soundness bounds (ABF26 §6)

Statement-layer for the §6 soundness bounds that do **not** depend on a
formal protocol object. The three protocol-level soundness lemmas
(`L6.6`, `L6.8`, `L6.10`) live alongside the protocol definitions in
`ToyProblem/Spec/General.lean` (C6.2) and
`ToyProblem/Spec/SimplifiedIOR.lean` (C6.9).

Items in this file:

* `ToyProblem.additive_code_supports_erasure_correction_grs25`
   — Lemma 6.5 [GRS25]: every additive code supports erasure correction
   with correction time `O((s · n)^3)`.

* `ToyProblem.simplified_iop_soundness_listDecoding_lb`
   — Lemma 6.12 [ABF26]: list-decoding-based lower bound on the
   soundness error of the simplified IOR `T'[C, t]` (Construction 6.9).
   Uses Claim B.1 via `Probability.exists_large_image_of_pairwise_collision_bound`.

* `ToyProblem.simplified_iop_soundness_ca_lb`
   — Lemma 6.13 [ABF26]: correlated-agreement-based lower bound on the
   soundness error of `T'[C, t]`.

Current status:

* **L6.5 is PROVEN** here (`additive_code_supports_erasure_correction_grs25`)
  in existence form (the polynomial-time content is the inert numeric
  parameter; the unique close-codeword decoder is unconditional).
* **L6.13 is PROVEN** (`simplified_iop_soundness_ca_lb`), under the linear-code
  encoder hypothesis on `C` (the regime `relation`/`relaxedRelation` demand).
* **L6.12 is PROVEN** (`simplified_iop_soundness_listDecoding_lb`): the §6.4.1
  winning-set construction (one Claim-B.1 application + the paper's injective
  affine reparametrisation of `S_v` into winning challenges) is fully
  machine-checked against the fixed-encoding `winningSetFor enc`. The bound is
  the **paper-exact** `N·|F|/(|F|+N−1)` (eprint 2026/680 §6.4.1, Lemma 6.12),
  under the paper's hypothesis `|F| > binom(N, 2)`. See its docstring.

L6.12/L6.13 are stated in coding-theory form (direct cardinality bounds on
`winningSet`); their protocol-level reading bounds the soundness of
`ToyProblem.SimplifiedIOR.reduction` from below.

**L6.12 status (paper-exact, 2026-06-04).** Fully proven and axiom-clean
(`#print axioms`: `[propext, Classical.choice, Quot.sound]`). The infrastructure:
`exists_dotProduct_image_lb` (the single Claim-B.1 application);
`exists_affine_injective_image` (the paper's injective `ψ : S_v → Γ`, which
carries the B.1 bound through verbatim — replacing the earlier lossy second B.1);
`claimB1_bound_to_real`; `mem_winningSetFor_of_agree`;
`affine_collision_card_le_one`; plus
`Pr_map_eq` / `prob_dotProduct_eq_zero_le` / `prob_uniform_le_inv_of_card_le_one`
in `Data/Probability/Instances.lean`.

**Faithfulness fix applied:** the statement is now against the **fixed-encoding**
`relaxedRelationFor enc` / `winningSetFor enc` (Definitions.lean). A Phase-4
review found the violation conjunct `¬ relaxedRelation (ℓ:=2)` is *false* against
ArkLib's existential-encoding `relation` — an adversary reparameterises the
linear constraint through a different linear encoding. The paper's `R_C` fixes
the code's encoding; against `relaxedRelationFor enc` the violation is exactly
`(μ₁,μ₂) ∉ S_v` and holds. The remaining coding-theory obligations (all provable)
are `hSmsgN` (the enc-injective codeword↔message bijection), `hmem` (membership
via `mem_winningSetFor_of_agree`), and the violation (via the agreement↔distance
reconciliation, template `mem_winningSet_zero_of_relClose`). The bound transfers
to the existential `winningSet` via `winningSetFor_subset`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-- **Finite-domain `iSup` attainment helper.** Over a finite domain, a
`⨆` into a conditionally-complete linear order with a bottom (here `ℕ∞`/
`ENNReal`) is attained at some point. Used to extract the CA- / list-maximiser
in `simplified_iop_soundness_ca_lb` and `simplified_iop_soundness_listDecoding_lb`. -/
lemma finite_iSup_eq_apply {α : Type*} [Finite α] [Nonempty α] {β : Type*}
    [ConditionallyCompleteLinearOrderBot β] (g : α → β) :
    ∃ a, (⨆ x, g x) = g a := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_max g
  exact ⟨a, le_antisymm (ciSup_le ha) (le_ciSup (Set.Finite.bddAbove (Set.finite_range g)) a)⟩

omit [DecidableEq F] in
/-- **Linear-functional collision bound** (ABF26 §6.4.1, Step 2 kernel count).

For a nonzero coefficient vector `w : Fin k → F` over a finite field, the
linear functional `v ↦ ∑ j, w j * v j : (Fin k → F) → F` is surjective, so
each of its fibers has cardinality `|F|^k / |F| = |F|^{k-1}`. Hence a
uniformly random `v` lands in the zero-fiber (the kernel hyperplane) with
probability exactly `1 / |F|`. This is the per-pair collision bound fed to
Claim B.1 in the proof of `simplified_iop_soundness_listDecoding_lb`. -/
lemma linearForm_collision_prob {k : ℕ} (w : Fin k → F) (hw : w ≠ 0) :
    Pr_{ let v ← $ᵖ (Fin k → F) }[(∑ j, w j * v j) = 0]
      = (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  -- The functional as an additive hom `L : (Fin k → F) →+ F`.
  let L : (Fin k → F) →+ F :=
    { toFun := fun v => ∑ j, w j * v j
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  -- `L` is surjective: some `w j₀ ≠ 0`, and `L (Pi.single j₀ (c / w j₀)) = c`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext fun j => by simpa using h j)
  have hLsurj : Function.Surjective L := by
    intro c
    refine ⟨(Pi.single j₀ (c / w j₀) : Fin k → F), ?_⟩
    change ∑ j, w j * (Pi.single j₀ (c / w j₀) : Fin k → F) j = c
    rw [Finset.sum_eq_single j₀]
    · rw [Pi.single_eq_same]; field_simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  -- Every fiber of `L` has the same cardinality; in particular the zero-fiber.
  -- `Pr[L v = 0] = |{v | L v = 0}| / |(Fin k → F)|`.
  rw [prob_uniform_eq_card_filter_div_card (F := (Fin k → F))
    (P := fun v => (∑ j, w j * v j) = 0)]
  -- Identify the filtered set as the zero-fiber of `L`.
  have hfilter : (Finset.univ.filter (fun v : Fin k → F => (∑ j, w j * v j) = 0))
      = (Finset.univ.filter (fun v : Fin k → F => L v = 0)) := rfl
  rw [hfilter]
  -- All fibers of the surjective hom `L` are equinumerous; sum over `F` of fiber
  -- cards is `|Fin k → F|`, so each (in particular zero) is `|Fin k → F| / |F|`.
  have hfib_const : ∀ x : F,
      (Finset.univ.filter (fun v : Fin k → F => L v = x)).card
        = (Finset.univ.filter (fun v : Fin k → F => L v = (0 : F))).card := by
    intro x
    exact AddMonoidHom.card_fiber_eq_of_mem_range L (hLsurj x) (hLsurj 0)
  -- `∑ x : F, |fiber x| = |Fin k → F|` (partition of the domain by `L`).
  have hpart : (Finset.univ : Finset (Fin k → F)).card
      = ∑ x : F, (Finset.univ.filter (fun v : Fin k → F => L v = x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (L v))
  have hsum : Fintype.card F *
      (Finset.univ.filter (fun v : Fin k → F => L v = (0:F))).card
      = Fintype.card (Fin k → F) := by
    rw [← Finset.card_univ (α := Fin k → F), hpart,
      Finset.sum_congr rfl (fun x _ => hfib_const x), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  -- From `|F| * |zeroFiber| = |Fin k → F|`, get `|zeroFiber| / |Fin k → F| = 1/|F|`.
  set Z : ℕ := (Finset.univ.filter (fun v : Fin k → F => L v = (0:F))).card with hZ
  have hcardF_pos : 0 < Fintype.card F := Fintype.card_pos
  have hcardF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast hcardF_pos.ne'
  have hdom_ne : (Fintype.card (Fin k → F) : ℝ≥0) ≠ 0 := by
    have : 0 < Fintype.card (Fin k → F) := Fintype.card_pos
    exact_mod_cast this.ne'
  -- `Z / |dom| = 1/|F|` in ℝ≥0, then cast to ENNReal.
  have hkey : ((Z : ℝ≥0) / (Fintype.card (Fin k → F) : ℝ≥0))
      = (1 : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul]
    have : (Fintype.card F : ℝ≥0) * (Z : ℝ≥0) = (Fintype.card (Fin k → F) : ℝ≥0) := by
      rw [hZ]; exact_mod_cast hsum
    rw [mul_comm] at this; rw [this]
  -- Convert the ℝ≥0 equality to the ENNReal goal.
  have hkeyE : (((Z : ℝ≥0) / (Fintype.card (Fin k → F) : ℝ≥0) : ℝ≥0) : ENNReal)
      = (1 : ENNReal) / (Fintype.card F : ENNReal) := by
    rw [hkey, ENNReal.coe_div hcardF_ne, ENNReal.coe_one, ENNReal.coe_natCast]
  rw [← hkeyE]
  norm_cast

omit [Field F] [Fintype F] in
/-- **Lemma 6.5 of [ABF26]** (= [GRS25]).

Every `F`-additive code `C : F^k → (F^s)^n` supports erasure correction
(in the sense of `CodingTheory.SupportsErasureCorrection`) with correction
time `O((s · n)^3)`. Equivalently: the predicate
`CodingTheory.SupportsErasureCorrection C ecor` holds for some
`ecor ≤ K · (s · n)^3`. We state the more permissive
"some `ecor` works" form here; pinning down the constant `K` requires
modelling the encoder concretely.

PROVEN (existence form). The paper's L6.5 / [GRS25] content is the
*polynomial running time* `O((s·n)^3)`; the `SupportsErasureCorrection`
predicate carries `ecor` as an inert numeric parameter (`_ecor`), so the
*existence* of a correct (not necessarily efficient) erasure-decoder is an
unconditional, in-tree fact: when fewer than `minDist C` symbols are erased
the agreeing codeword is unique (two such codewords would differ only on
the erased coordinates, giving Hamming distance `< minDist C`, forcing
equality), so a classical decoder choosing that witness is well-defined.
We take `ecor = 0` (the numeric time bound is not operationally modelled). -/
theorem additive_code_supports_erasure_correction_grs25
    (C : Set (ι → F)) :
    ∃ ecor : ℕ, CodingTheory.SupportsErasureCorrection C ecor := by
  classical
  -- The "good witness" predicate: a codeword agreeing with `f` off the
  -- erasures, with strictly fewer than `minDist C` erasures.
  set erasureCard : (ι → Option F) → ℕ :=
    fun f ↦ (Finset.univ.filter (fun i ↦ f i = none)).card with hEC
  let good : (ι → Option F) → (ι → F) → Prop :=
    fun f u ↦ u ∈ C ∧ (∀ i, f i = some (u i) ∨ f i = none) ∧ erasureCard f < Code.minDist C
  -- Uniqueness: two good witnesses for the same `f` coincide.
  have huniq : ∀ (f : ι → Option F) (u u' : ι → F), good f u → good f u' → u = u' := by
    intro f u u' ⟨huC, hua, hue⟩ ⟨hu'C, hu'a, _⟩
    by_contra hne
    -- The disagreement set of `u, u'` is contained in the erasure set of `f`.
    have hsub : (Finset.univ.filter (fun i ↦ u i ≠ u' i)) ⊆
        (Finset.univ.filter (fun i ↦ f i = none)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      -- if `f i ≠ none` then `f i = some (u i) = some (u' i)`, so `u i = u' i`.
      rcases hua i with hfi | hfi
      · rcases hu'a i with hfi' | hfi'
        · exact absurd (Option.some.inj (hfi.symm.trans hfi')) hi
        · rw [hfi] at hfi'; exact absurd hfi' (by simp)
      · exact hfi
    have hdist_le : Δ₀(u, u') ≤ erasureCard f := by
      rw [hEC]; exact Finset.card_le_card hsub
    -- But distinct codewords are `≥ minDist C` apart.
    have hge : Code.minDist C ≤ Δ₀(u, u') := by
      have hd : ‖C‖₀ ≤ Δ₀(u, u') := pairDist_ge_code_mindist_of_ne huC hu'C hne
      rwa [dist_eq_minDist] at hd
    exact absurd (lt_of_le_of_lt (le_trans hge hdist_le) hue) (lt_irrefl _)
  -- The decoder: pick the (unique) good witness when one exists, else `none`.
  let E : (ι → Option F) → Option (ι → F) :=
    fun f ↦ if h : ∃ u, good f u then some h.choose else none
  refine ⟨0, E, fun f ↦ ⟨?_, ?_⟩⟩
  · -- (i) recovery clause
    intro u huC hagree hsmall
    have hgood : good f u := ⟨huC, hagree, hsmall⟩
    have hex : ∃ u, good f u := ⟨u, hgood⟩
    change E f = some u
    simp only [E, dif_pos hex]
    exact congrArg some (huniq f hex.choose u hex.choose_spec hgood)
  · -- (ii) failure clause
    intro hno
    have : ¬ ∃ u, good f u := by
      rintro ⟨u, huC, hagree, hsmall⟩
      exact hno ⟨u, huC, hagree, hsmall⟩
    change E f = none
    simp only [E, dif_neg this]

/-- **L6.12 Step-4 arithmetic helper (B.1 bound is `≤ |F|`).** The list-decoding
soundness lower bound `N·|F| / (|F| + N − 1)` never exceeds `|F|`: indeed
`(N − 1)(|F| − 1) ≥ 0` gives `N·|F| ≤ |F|·(|F| + N − 1)`, and dividing by the
positive denominator yields the claim. (Real-arithmetic core of the
faithfulness note: the bound is meaningful only as a soundness-error lower
bound, never larger than `|F|`.) PROVEN, axiom-clean. -/
lemma listDecoding_lb_le_card (N : ℕ) (M : ℝ) (hM : (1 : ℝ) ≤ M) :
    ((N : ℝ) * M) / (M + (N : ℝ) - 1) ≤ M := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; positivity
  · have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hden_pos : 0 < M + (N : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ) - 1) (by linarith : (0:ℝ) ≤ M - 1)]

/-- **L6.12 Step-4 arithmetic helper (B.1 bound is `≥ 1` when the list is
nonempty).** When `N ≥ 1` and `|F| ≥ 1`, the bound `N·|F| / (|F| + N − 1)` is
at least `1`: the numerator dominates the denominator by `(N − 1)(|F| − 1) ≥ 0`.
So a faithful attack instance must exhibit at least one winning challenge.
PROVEN, axiom-clean. -/
lemma one_le_listDecoding_lb (N : ℕ) (M : ℝ) (hM : (1 : ℝ) ≤ M) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ ((N : ℝ) * M) / (M + (N : ℝ) - 1) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden_pos : 0 < M + (N : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hden_pos, one_mul]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ) - 1) (by linarith : (0:ℝ) ≤ M - 1)]

/-- **L6.12 Step-4 reduction helper (empty-list branch).** When the maximised
list size is `0`, the list-decoding lower bound `N·|F| / (|F| + N − 1)` collapses
to `0`, so *any* attack instance discharges the bound (cardinalities are
nonnegative). This is the honest `N = 0` branch of L6.12 — vacuous *bound*, not
a vacuous *witness*: it does not claim a large winning set. PROVEN, axiom-clean. -/
lemma listDecoding_lb_zero_of_card_zero (N : ℕ) (M : ℝ) (hN : N = 0) :
    ((N : ℝ) * M) / (M + (N : ℝ) - 1) ≤ 0 := by
  subst hN; simp

/-- **L6.12 Step-2 collision bridge** (ABF26 §6.4.1, pair form). For two
*distinct* message pairs `(m₀, m₁) ≠ (m₀', m₁')` over a finite field, the
"evaluation map" `v ↦ (⟨m₀, v⟩, ⟨m₁, v⟩) : (Fin k → F) → F × F` collides on the
two pairs (i.e. `φ_v(m₀,m₁) = φ_v(m₀',m₁')`) with probability at most `1/|F|`
over a uniform `v ←$ F^k`. Proof: at least one difference vector
`m₀ − m₀'` / `m₁ − m₁'` is nonzero; the *joint* collision event implies the
*single*-functional zero event for that difference, whose probability is
exactly `1/|F|` by `linearForm_collision_prob`. This is precisely the per-pair
collision hypothesis fed to Claim B.1
(`Probability.exists_large_image_of_pairwise_collision_bound`) in Step 3, with
`S = Fin N` the codeword list, `T = F × F`, and `ε = 1/|F|`. PROVEN,
axiom-clean. -/
lemma pair_linearForm_collision_le {k : ℕ}
    (m0 m1 m0' m1' : Fin k → F) (hne : (m0, m1) ≠ (m0', m1')) :
    Pr_{ let v ← $ᵖ (Fin k → F) }[
      (decide ((∑ j, m0 j * v j, ∑ j, m1 j * v j)
             = (∑ j, m0' j * v j, ∑ j, m1' j * v j)) : Prop)]
      ≤ (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  -- At least one of the two message-difference vectors is nonzero.
  have hdiff : (m0 - m0' ≠ 0) ∨ (m1 - m1' ≠ 0) := by
    by_contra h
    push_neg at h
    obtain ⟨h0, h1⟩ := h
    apply hne
    have e0 : m0 = m0' := by funext j; have := congrFun h0 j; simpa [sub_eq_zero] using this
    have e1 : m1 = m1' := by funext j; have := congrFun h1 j; simpa [sub_eq_zero] using this
    rw [e0, e1]
  rcases hdiff with hd | hd
  · -- Nonzero first-coordinate difference `w = m₀ − m₀'`.
    refine le_trans (Pr_le_Pr_of_implies ($ᵖ (Fin k → F)) _
      (fun v => (decide ((∑ j, (m0 - m0') j * v j) = 0) : Prop)) ?_) ?_
    · intro v hev
      simp only [decide_eq_true_eq, Prod.mk.injEq] at hev ⊢
      have h0 := hev.1
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [h0]; ring
    · have := linearForm_collision_prob (m0 - m0') hd
      simpa using le_of_eq this
  · -- Nonzero second-coordinate difference `w = m₁ − m₁'`.
    refine le_trans (Pr_le_Pr_of_implies ($ᵖ (Fin k → F)) _
      (fun v => (decide ((∑ j, (m1 - m1') j * v j) = 0) : Prop)) ?_) ?_
    · intro v hev
      simp only [decide_eq_true_eq, Prod.mk.injEq] at hev ⊢
      have h1 := hev.2
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [h1]; ring
    · have := linearForm_collision_prob (m1 - m1') hd
      simpa using le_of_eq this

omit [DecidableEq F] in
/-- **Lemma 6.12 of [ABF26]** (list-decoding lower bound on the simplified IOR).

Coding-theory form: if `C` is a linear code (the image of an `F`-linear
encoding of message dimension `k`), `|Λ(C^{≡2}, δ)| < |F|` and
`(|Λ(C^{≡2}, δ)| choose 2) < |F|` (the paper's `|F| > binom(|Λ|, 2)`),
then there exist witnesses `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying
**outside** the relaxed relation `R̃_{C,δ}^2` (the `violates` conjunct), for
which the winning challenge set `Ω^{f_1,f_2}_{v,μ_1,μ_2}` (Definition 6.11)
has at least `|Λ(C^{≡2}, δ)| · |F| / (|F| + |Λ(C^{≡2}, δ)| − 1)` elements.

The protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9, `ToyProblem.SimplifiedIOR.reduction`) is
at least `|Λ(C^{≡2}, δ)| / (|F| + |Λ(C^{≡2}, δ)| − 1)`.

## Statement provenance (paper-exact, strengthened 2026-06-04)

Writing `N := |Λ(C^{≡2}, δ)|`, `F := |F|`, the **final** soundness bound in
ABF26 §6.4.1 (eprint 2026/680 §6.4.1, p.36; Lemma 6.12) is
`N / (F + N − 1)`, hence the winning-set cardinality bound `N · F / (F + N − 1)`.
The paper's hypothesis is `|F| > binom(N, 2)` (page 35, statement of Lemma 6.12).

**Adjudication (2026-06-04, eprint 2026/680 p.36 vs. local extract
`research/proximity-prize/artifacts/2026-680.txt` lines 1660–1700).** The paper
applies Claim B.1 **once** — the first application gives
`|S_v| ≥ N / (1 + (N−1)/F) = N·F/(F+N−1)` — and then exhibits an **injective**
affine map `ψ : S_v → Γ_{μ₁,μ₂}`, so `|Γ_{μ₁,μ₂}| ≥ |S_v| ≥ N·F/(F+N−1)`. The
injectivity (NOT a second Claim-B.1 pass) is what carries the first-B.1 bound
through *verbatim*. The previously in-tree `N·F/(F+2N)` used a **second**, lossy
B.1 application on the affine map (giving `F·|S_v|/(F+|S_v|−1)`) and a denominator
chain `z ↦ z/(F+z−1)`; that overestimated the collision slack and undershot the
paper. Replacing the second B.1 with the paper's injective `ψ` recovers the exact
`N·F/(F+N−1)`. The injection requires `|F| > binom(N, 2)` (so a `μ₁` avoiding the
`≤ binom(|S_v|, 2)` bad values exists); this is exactly the paper's hypothesis.

## Proof recipe (ABF26 §6.4.1, with Claim B.1 machine-checked)

The intermediate `|S_v| ≥ N · F / (F + N − 1)` is exactly the conclusion of
Claim B.1 specialised to `|S| = N`, `|T| = F`, `ε = 1/F`:
`N / (1 + (N − 1) · (1/F)) = N · F / (F + N − 1)`, so the proof skeleton is:

1. **Build the list.** Enumerate `Λ(C^{≡2}, δ)` as pairs `(W₀(λ), W₁(λ))` of
   `δ`-close codewords in `C` (paper `(v_0(λ), v_1(λ))`). Pick `v ∈ F^k` and
   define `φ_v : λ ↦ (⟨W₀(λ), v⟩, ⟨W₁(λ), v⟩)`.

2. **Pairwise collision bound.** For distinct list entries the linear
   functional `⟨·, v⟩` collides with probability `≤ 1/F` over `v ←$ F^k`.

3. **Apply Claim B.1 (the only B.1 use).** Obtain `v*` with
   `|S_{v*}| ≥ N·F/(F+N−1)` (`exists_dotProduct_image_lb` + `claimB1_bound_to_real`).

4. **Affine injection + violation.** Pick `μ₂` not a second coordinate in
   `S_{v*}` and a `μ₁` (avoiding the `≤ binom(|S_{v*}|, 2) < |F|` bad values)
   under which the affine map `(a₁,a₂) ↦ (μ₁−a₁)/(a₂−μ₂)` is **injective** on
   `S_{v*}` (`exists_affine_injective_image`). Then the winning set has size
   `≥ |S_{v*}| ≥ N·F/(F+N−1)`. Since `(μ₁,μ₂) ∉ S_{v*}`, the instance violates
   `R̃_{C,δ}^2` (the `violates` conjunct).

The encoding hypothesis is `∃ enc, Function.Injective enc ∧ range enc = C` — the
faithful "linear code of dimension `k`" assumption (an injective `F`-linear
encoding onto `C`), which is what makes `Λ(C^{≡2}, δ)` enumerable by *message*
pairs `F^k × F^k` (the inner products `⟨·, v⟩` of paper step 1 live on messages).
This strengthens L6.13's `range enc = C` and matches the linear `encode` field of
`ToyProblem.relation`.

The statement is against the **fixed-encoding** relation and winning set
(`relaxedRelationFor enc`, `winningSetFor enc`), with `enc` the code's injective
`F`-linear encoding (`Set.range enc = C`). This is the paper's `R_C`. (Against
ArkLib's existential-encoding `relaxedRelation` the violation conjunct is false —
an adversary reparameterises the constraint through another encoding. The
quantitative bound transfers to the existential `winningSet` via
`winningSetFor_subset`.)

  * **Step 4 (winning-set construction) — RESIDUAL.** Even with the
    linear-encoder hypothesis (cf. `simplified_iop_soundness_ca_lb`, which
    closes the analogous `relation`-from-membership wall via `hEnc`), the
    L6.12 conclusion bounds a *single* `winningSet C δ v* μ₁ μ₂ f₁ f₂` over
    challenges `γ ∈ F`, whereas B.1 produces a large *image set* of pairs
    `(μ₁(λ), μ₂(λ)) ∈ F × F` indexed by the codeword list. Bridging the two
    is the genuine §6.4.1 attack combinatorics: from the list one must build
    a concrete attack instance and an injection from image pairs into winning
    challenges (`μ_new = μ₁ + γ·μ₂` solved for a unique `γ` per pair under
    `|F| > binom(N, 2)`). This is a multi-step protocol-attack development,
    not a mechanical application of B.1, and is left for follow-up.

## Faithfulness note (2026-06): why a trivial witness is INADMISSIBLE here

The Lean conclusion is an *existential* over `(v, μ₁, μ₂, f₁, f₂)` and — unlike
the paper's prose — does **not** carry the §6.4 side condition that `(f₁, f₂)`
violate the relaxed relation `R̃²_{C,δ}`. The arithmetic bound is weak:
`N·|F| / (|F| + N − 1) ≤ |F|` for all `N ≥ 0` (since `N ≤ |F| + N − 1` whenever
`|F| ≥ 1`). Hence the all-zero instance `v = 0, μ₁ = μ₂ = 0, f₁ = f₂ = 0`
*formally* discharges the goal: under `hEnc` the zero word lies in `C` and
satisfies `relation C 0 0 0` (via the `hrel_of_mem` bridge proved in
`simplified_iop_soundness_ca_lb`), so `winningSet C δ 0 0 0 0 0 = F` and its
`ncard = |F| ≥ N·|F|/(|F|+N−1)`. **This trivial proof is deliberately NOT
submitted**: it is vacuous (the all-zero `(f₁,f₂)` is *inside* `R̃²`, the exact
instance the paper excludes), it bypasses Steps 1–3 entirely, and it
misrepresents L6.12's content (the bound is only meaningful as a *lower bound
on the soundness error realised by a violating attack instance*). A faithful
proof must (a) add the §6.4 violation hypothesis `¬ R̃²_{C,δ}(f₁,f₂)` to the
statement — which blocks the all-zero witness — and (b) realise the genuine
Step-4 maximiser+injection attack. Both are deferred together; the residual
below is that faithful proof, not the vacuous discharge.

Tagged sorry (`paper-proof-owed`, step 4 only) — ABF26's OWN result
(§6.4.1). Steps 1–3 are realised by in-tree lemmas; the residual is the
list→challenge winning-set injection, which additionally needs the
`hEnc` linear-encoder hypothesis (as in `simplified_iop_soundness_ca_lb`)
and the §6.4 violation hypothesis (see the faithfulness note above).

## Integrated Step-2/Step-4 helpers (PROVEN, axiom-clean)

The following sorry-free, axiom-clean helpers (immediately above) are the
genuine partial progress toward this residual; the main `sorry` is *not*
discharged, but these are reusable by whoever completes Step 4:

  * `listDecoding_lb_le_card` : `N·|F| / (|F| + N − 1) ≤ |F|` (the loose-bound
    clamp / faithfulness-note arithmetic core).
  * `one_le_listDecoding_lb` : `1 ≤ N·|F| / (|F| + N − 1)` for `N, |F| ≥ 1`
    (a faithful attack must exhibit ≥ 1 winning challenge).
  * `listDecoding_lb_zero_of_card_zero` : `N = 0 ⇒ N·|F| / (|F| + N − 1) ≤ 0`
    (honest empty-list branch — vacuous *bound*, never a vacuous *witness*).
  * `pair_linearForm_collision_le` : the Step-2 *pair*-collision bound feeding
    Claim B.1 — distinct message pairs collide under `v ↦ (⟨m₀,v⟩,⟨m₁,v⟩)`
    with probability `≤ 1/|F|`, via the proven `linearForm_collision_prob`. -/
theorem simplified_iop_soundness_listDecoding_lb {k : ℕ}
    [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (hinj : Function.Injective enc)
    (hC : Set.range enc = C)
    (hF : ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
      < Fintype.card F)
    (hFchoose : Nat.choose (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat 2
      < Fintype.card F) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ¬ relaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ) - 1) := by
  classical
  set Cint : Set (Matrix ι (Fin 2) F) := interleavedCodeSet (κ := Fin 2) C with hCint
  -- Maximising matrix `fStar` for the list size (finite supremum, as in L6.13).
  obtain ⟨fStar, hfStar⟩ := Finite.exists_max
    (fun f : ι → Fin 2 → F ↦ (closeCodewordsRel Cint f (δ : ℝ)).ncard)
  set N : ℕ := (Lambda Cint (δ : ℝ)).toNat with hNdef
  have hNeq : N = (closeCodewordsRel Cint fStar (δ : ℝ)).ncard := by
    rw [hNdef, Lambda,
      show (⨆ f : ι → Fin 2 → F, ((closeCodewordsRel Cint f (δ : ℝ)).ncard : ℕ∞))
          = ((closeCodewordsRel Cint fStar (δ : ℝ)).ncard : ℕ∞) from
        le_antisymm (iSup_le fun f ↦ by exact_mod_cast hfStar f)
          (le_iSup (fun f ↦ ((closeCodewordsRel Cint f (δ : ℝ)).ncard : ℕ∞)) fStar),
      ENat.toNat_coe]
  set f₁ : ι → F := fun i ↦ fStar i 0 with hf1
  set f₂ : ι → F := fun i ↦ fStar i 1 with hf2
  have hcardF1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hNltF : N < Fintype.card F := by exact_mod_cast hF
  have hNchoose : Nat.choose N 2 < Fintype.card F := hFchoose
  -- Message-pair enumeration of `Λ(C^{≡2}, δ, (f₁,f₂))`.
  set Smsg : Finset ((Fin k → F) × (Fin k → F)) :=
    Finset.univ.filter (fun p ↦ encStack enc p ∈ closeCodewordsRel Cint fStar (δ : ℝ)) with hSmsg
  -- ENUMERATION (bijection codewords ↔ message pairs via the injective `enc`).
  -- `encStack enc` is injective: its two columns determine `enc m.1, enc m.2`, hence (by
  -- `hinj`) `m.1, m.2`.
  have hencStack_inj : Function.Injective (encStack enc) := by
    intro p q hpq
    have h1 : enc p.1 = enc q.1 := by
      rw [← encStack_transpose_zero enc p, ← encStack_transpose_zero enc q, hpq]
    have h2 : enc p.2 = enc q.2 := by
      rw [← encStack_transpose_one enc p, ← encStack_transpose_one enc q, hpq]
    exact Prod.ext (hinj h1) (hinj h2)
  have hSmsgN : Smsg.card = N := by
    -- ABF26-L6.12 enumeration: `encStack enc` is a bijection from the message pairs `Smsg`
    -- onto `closeCodewordsRel C^{≡2} fStar δ`. Injective by `hencStack_inj`; surjective
    -- since every close codeword stack `V` has both columns in `C = range enc`.
    rw [hNeq]
    -- The image of `Smsg` under `encStack enc` is exactly the close-codewords set.
    have himg : (encStack enc) '' (Smsg : Set ((Fin k → F) × (Fin k → F)))
        = (closeCodewordsRel Cint fStar (δ : ℝ) : Set (Matrix ι (Fin 2) F)) := by
      ext V
      simp only [Set.mem_image, Finset.mem_coe, hSmsg, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp
      · intro hV
        -- `V`'s columns are codewords: `V.transpose 0 = enc m₀`, `V.transpose 1 = enc m₁`.
        have hcol0 : V.transpose 0 ∈ Set.range enc := by rw [hC]; exact hV.1 0
        have hcol1 : V.transpose 1 ∈ Set.range enc := by rw [hC]; exact hV.1 1
        obtain ⟨m₀, hm₀⟩ := hcol0
        obtain ⟨m₁, hm₁⟩ := hcol1
        refine ⟨(m₀, m₁), ?_, ?_⟩
        · -- `encStack enc (m₀, m₁) ∈ closeCodewordsRel`, since it equals `V`.
          have hVeq : encStack enc (m₀, m₁) = V := by
            funext i j; fin_cases j
            · change encStack enc (m₀, m₁) i 0 = V i 0
              rw [encStack_apply_zero]; exact congrFun hm₀ i
            · change encStack enc (m₀, m₁) i 1 = V i 1
              rw [encStack_apply_one]; exact congrFun hm₁ i
          rw [hVeq]; exact hV
        · funext i j; fin_cases j
          · change encStack enc (m₀, m₁) i 0 = V i 0
            rw [encStack_apply_zero]; exact congrFun hm₀ i
          · change encStack enc (m₀, m₁) i 1 = V i 1
            rw [encStack_apply_one]; exact congrFun hm₁ i
    calc Smsg.card
        = (Smsg : Set ((Fin k → F) × (Fin k → F))).ncard := (Set.ncard_coe_finset _).symm
      _ = (encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard :=
          (Set.ncard_image_of_injective _ hencStack_inj).symm
      _ = (closeCodewordsRel Cint fStar (δ : ℝ)).ncard := by rw [himg]; rfl
  have hcardSmsg : Fintype.card ↥Smsg = N := by rw [Fintype.card_coe, hSmsgN]
  -- FIRST B.1: a constraint vector `v` with a large inner-product image `S_v`.
  obtain ⟨v, hv⟩ :=
    exists_dotProduct_image_lb (Subtype.val : ↥Smsg → (Fin k → F) × (Fin k → F))
      Subtype.coe_injective
  rw [hcardSmsg] at hv
  set Sv : Finset (F × F) := Finset.univ.image
    (fun s : ↥Smsg ↦ ((∑ j, (s : (Fin k → F) × (Fin k → F)).1 j * v j),
                       (∑ j, (s : (Fin k → F) × (Fin k → F)).2 j * v j))) with hSvdef
  -- `|S_v| ≤ N < |F|`.
  have hSvle : Sv.card ≤ N := by
    rw [← hcardSmsg, hSvdef]; exact le_trans Finset.card_image_le (le_of_eq (Finset.card_univ))
  have hSvltF : Sv.card < Fintype.card F := lt_of_le_of_lt hSvle hNltF
  have hSvchoose : Nat.choose Sv.card 2 < Fintype.card F :=
    lt_of_le_of_lt (Nat.choose_le_choose 2 hSvle) hNchoose
  -- AFFINE INJECTION (paper-exact step 4): pick `μ₂` off the second coordinates and a
  -- `μ₁` under which the affine reparametrisation `ψ` is INJECTIVE on `S_v`. Injectivity
  -- (not a lossy second Claim-B.1) carries the first-B.1 bound `|S_v|` through verbatim.
  obtain ⟨μ₁, μ₂, hμ₂off, _hψinj, hwincard⟩ :=
    exists_affine_injective_image Sv hSvltF hSvchoose
  set winImg : Finset F := Sv.image (fun p ↦ (μ₁ - p.1) / (p.2 - μ₂)) with hwinImg
  refine ⟨v, μ₁, μ₂, f₁, f₂, ?_, ?_⟩
  · -- VIOLATION CONJUNCT (against the fixed-encoding `relaxedRelationFor enc`).
    --
    -- The paper's violation `Δ((f₁,f₂), R²[x]) > δ` is, under the code's fixed
    -- encoding, exactly `(μ₁,μ₂) ∉ S_v`. PROOF: suppose `relaxedRelationFor enc`
    -- holds — extract `Wstar` with `Wstar i = enc (M i)` and `∑ⱼ M i j vⱼ = μ i`
    -- (so `⟨M 0, v⟩ = μ₁`, `⟨M 1, v⟩ = μ₂`), δ-close to `![f₁,f₂]` on a set `S'`.
    -- Then `encStack enc (M 0, M 1) = Wstar` is δ-close to `fStar`, so it lies in
    -- `closeCodewordsRel Cint fStar δ` (columns `enc (M i) ∈ C` via `hC`; distance
    -- from the `S'` agreement, reverse of the reconciliation used for `hmem`).
    -- Hence `(M 0, M 1) ∈ Smsg`, so `φ_v(M 0, M 1) = (μ₁, μ₂) ∈ S_v` — contradicting
    -- `hμ₂off` (`(μ₁,μ₂).2 = μ₂` is a second coordinate of `S_v`). ABF26-L6.12.
    rintro ⟨Wstar, ⟨M, hWeq, hconstr⟩, S', hS'card, hS'ag⟩
    -- `(M 0, M 1) ∈ Smsg`: build the agreement set `S'` for `encStack enc (M 0, M 1)`.
    have hmemSmsg : (M 0, M 1) ∈ Smsg := by
      rw [hSmsg, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [encStack_mem_closeCodewordsRel_iff enc hC _hδ_lt]
      refine ⟨S', hS'card, fun i hi ↦ ⟨?_, ?_⟩⟩
      · -- `fStar i 0 = f₁ i = ![f₁,f₂] 0 i = Wstar 0 i = enc (M 0) i = enc (M 0,M 1).1 i`
        have hag : f₁ i = Wstar 0 i := hS'ag 0 i hi
        -- `f₁ i = fStar i 0` definitionally.
        change fStar i 0 = enc (M 0) i
        rw [show fStar i 0 = f₁ i from rfl, hag, hWeq 0]
      · have hag : f₂ i = Wstar 1 i := hS'ag 1 i hi
        change fStar i 1 = enc (M 1) i
        rw [show fStar i 1 = f₂ i from rfl, hag, hWeq 1]
    -- `(μ₁, μ₂) ∈ S_v`, contradicting `hμ₂off`.
    have hpair : ((∑ j, (M 0) j * v j), (∑ j, (M 1) j * v j)) = (μ₁, μ₂) := by
      have h0 : ∑ j, (M 0) j * v j = μ₁ := hconstr 0
      have h1 : ∑ j, (M 1) j * v j = μ₂ := hconstr 1
      rw [h0, h1]
    have hμ₂mem : (μ₁, μ₂) ∈ Sv := by
      rw [hSvdef, Finset.mem_image]
      exact ⟨⟨(M 0, M 1), hmemSmsg⟩, Finset.mem_univ _, hpair⟩
    exact hμ₂off (μ₁, μ₂) hμ₂mem rfl
  · -- CARDINALITY CHAIN.
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · -- N = 0: the bound is `0 ≤ ncard`, trivially true.
      rw [hN0, ge_iff_le]; simp
    -- Main case N ≥ 1.
    -- MEMBERSHIP: every winning challenge in `winImg` lies in the winning set.
    have hmem : (winImg : Set F) ⊆ winningSetFor enc δ v μ₁ μ₂ f₁ f₂ := by
      -- ABF26-L6.12 membership: each `γ = (μ₁−a)/(b−μ₂)` with `(a,b) = φ_v(m)`,
      -- `m ∈ Smsg`, is winning via `mem_winningSetFor_of_agree` (message `m.1+γ•m.2`,
      -- constraint `⟨m.1+γ·m.2, v⟩ = a+γb = μ₁+γμ₂`, agreement from `encStack`
      -- closeness + `enc`-linearity). Uses the same agreement-cols reconciliation
      -- as `mem_winningSet_zero_of_relClose`.
      intro γ hγ
      rw [Finset.coe_image, Set.mem_image] at hγ
      obtain ⟨⟨a, b⟩, hab, hγeq⟩ := hγ
      -- `hγeq : (μ₁ - a)/(b - μ₂) = γ`
      rw [hSvdef, Finset.mem_coe, Finset.mem_image] at hab
      obtain ⟨s, _, hsab⟩ := hab
      -- `m = ↑s` is a message pair in `Smsg`; extract its agreement set `S'`.
      set m : (Fin k → F) × (Fin k → F) := (s : (Fin k → F) × (Fin k → F)) with hm
      have hmSmsg : m ∈ Smsg := s.2
      rw [hSmsg, Finset.mem_filter] at hmSmsg
      obtain ⟨S', hS'card, hS'ag⟩ :=
        (encStack_mem_closeCodewordsRel_iff enc hC _hδ_lt m).mp hmSmsg.2
      -- The image point: `a = ∑ⱼ m.1 ⱼ vⱼ`, `b = ∑ⱼ m.2 ⱼ vⱼ`.
      have hab_eq : (∑ j, m.1 j * v j) = a ∧ (∑ j, m.2 j * v j) = b := by
        have := Prod.ext_iff.mp hsab; exact ⟨this.1, this.2⟩
      obtain ⟨ha, hb⟩ := hab_eq
      -- `b ≠ μ₂` (so the affine challenge is well-defined).
      have hbμ₂ : b ≠ μ₂ := hμ₂off (a, b) (by
        rw [hSvdef, Finset.mem_image]; exact ⟨s, Finset.mem_univ _, hsab⟩)
      -- Apply the membership helper with message `m.1 + γ • m.2`.
      refine mem_winningSetFor_of_agree enc (m := m.1 + γ • m.2) ?_ S' hS'card ?_
      · -- constraint `⟨m.1 + γ•m.2, v⟩ = a + γ b = μ₁ + γ μ₂`.
        have hsum : (∑ j, (m.1 + γ • m.2) j * v j) = a + γ * b := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hb]
        rw [hsum]
        -- `γ = (μ₁ - a)/(b - μ₂)`, `b ≠ μ₂` ⇒ `γ*(b - μ₂) = μ₁ - a` ⇒ `a + γ b = μ₁ + γ μ₂`.
        have hbsub : b - μ₂ ≠ 0 := sub_ne_zero.mpr hbμ₂
        rw [← hγeq]
        field_simp
        ring
      · -- agreement: on `S'`, `f₁ i + γ•f₂ i = enc m.1 i + γ•enc m.2 i = enc (m.1+γ•m.2) i`.
        intro i hi
        obtain ⟨h0, h1⟩ := hS'ag i hi
        have henc : enc (m.1 + γ • m.2) i = enc m.1 i + γ * enc m.2 i := by
          rw [map_add, map_smul]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [henc]
        -- `f₁ i = fStar i 0 = enc m.1 i`, `f₂ i = fStar i 1 = enc m.2 i`.
        rw [show f₁ i = fStar i 0 from rfl, show f₂ i = fStar i 1 from rfl, h0, h1]
    -- FIRST B.1 + bridge: `N·F/(F+N−1) ≤ |S_v|` (the paper's `|S_v| ≥ N·F/(F+N−1)`).
    have hAreal : (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) ≤ (Sv.card : ℝ) :=
      claimB1_bound_to_real hcardF1 hN1 hv
    -- INJECTIVITY (paper step 4): `|winImg| = |S_v|`, so the first-B.1 bound passes through
    -- VERBATIM — no lossy `z ↦ z/(F+z−1)` second pass. This is the paper-exact denominator.
    have hwinge : (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) ≤ (winImg.card : ℝ) := by
      refine le_trans hAreal (le_of_eq ?_)
      rw [hwinImg]; exact_mod_cast hwincard.symm
    -- winImg ⊆ winningSet ⇒ |winImg| ≤ ncard(winningSet).
    have hncard : (winImg.card : ℝ) ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) := by
      have : winImg.card ≤ (winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard := by
        rw [← Set.ncard_coe_finset winImg]
        exact Set.ncard_le_ncard hmem (Set.toFinite _)
      exact_mod_cast this
    rw [ge_iff_le]
    exact le_trans hwinge hncard

omit [Fintype F] in
/-- **Membership helper for the §6.4 attacks.** If `C` is a linear code (the
range of an `F`-linear encoding `enc` of message dimension `k`) and the line
`f₁ + γ·f₂` is `δ`-close to `C`, then `γ` is a winning challenge for the
all-zero instance `(v, μ₁, μ₂) = (0, 0, 0)` (Definition 6.11). This is the
inclusion `S ⊆ Ω^{f₁,f₂}_{0,0,0}` from the proof of **Lemma 6.13 of [ABF26]**
(§6.4.2), generalised to any line. -/
theorem mem_winningSet_zero_of_relClose {k : ℕ} [Nonempty ι] {C : Set (ι → F)}
    {δ : ℝ≥0} (_hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (hC : Set.range enc = C)
    (f₁ f₂ : ι → F) {γ : F} (hγ : δᵣ(f₁ + γ • f₂, C) ≤ δ) :
    γ ∈ winningSet C δ (0 : Fin k → F) 0 0 f₁ f₂ := by
  classical
  rw [winningSet, Set.mem_setOf_eq]
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hγ
  obtain ⟨w, hwC, hwd⟩ := hγ
  obtain ⟨m, hm⟩ : ∃ m, enc m = w := by rw [← hC] at hwC; exact hwC
  refine ⟨fun _ ↦ w, ⟨fun _ ↦ m, ⟨enc, fun m' ↦ hC ▸ ⟨m', rfl⟩, fun i ↦ by simp [hm]⟩,
      fun i ↦ by simp⟩, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols] at hwd
  obtain ⟨S, hScard, hSagree⟩ := hwd
  refine ⟨S, ?_, ?_⟩
  · -- `(1 - δ)·|ι| ≤ |S|` in ℝ, from the `|ι| - ⌊δ|ι|⌋ ≤ |S|` agreement bound.
    have h2 := (relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mp hScard
    have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by rw [NNReal.coe_sub _hδ_lt.le]; simp
    have := (NNReal.coe_le_coe.mpr h2)
    rw [NNReal.coe_mul, e] at this
    push_cast at this ⊢
    linarith [this]
  · intro i j hj
    have hag := (hSagree j).1 hj
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hag

/-- **Lemma 6.13 of [ABF26]** (correlated-agreement lower bound on the simplified IOR).

Coding-theory form: if `C` is a linear code (range of an `F`-linear encoding
`enc` of message dimension `k`) and the correlated-agreement error is positive,
then there exist `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying **outside**
the relaxed relation `R̃_{C,δ}^2` (the `violates` conjunct) whose winning
challenge set has size at least `ε_ca(C, δ) · |F|`.

Protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9) is at least `ε_ca(C, δ)`.

Proof (ABF26 §6.4.2, now machine-checked): the CA error is a supremum over a
finite type of word-stacks, hence attained at some `u = (f_1, f_2)`; since the
error is positive, `u` is *not* jointly `δ`-close to `C^{≡2}` — this is exactly
the violation `¬ R̃_{C,δ}^2` (via `jointAgreement_iff_jointProximity`). Its
value is then `Pr_γ[Δ(f_1 + γ·f_2, C) ≤ δ] = |S|/|F|` with `S = {γ : Δ(f_1 +
γ·f_2, C) ≤ δ}`, and `S ⊆ Ω^{f_1,f_2}_{0,0,0}` (`mem_winningSet_zero_of_relClose`).
The `0 < ε_ca` hypothesis matches the paper's "if not, the statement holds
vacuously". The bound is in terms of `ε_ca` (correlated agreement) rather than
`ε_mca`; the latter would be qualitatively stronger but no attack reaching
`ε_mca > ε_ca` is currently known (Remark 6.14). -/
theorem simplified_iop_soundness_ca_lb {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C)
    (hca : 0 < epsCA (F := F) (A := F) C δ δ) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
        ≥ epsCA (F := F) (A := F) C δ δ * (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨enc, hC⟩ := hClin
  -- The CA error is attained at some word-stack `u` (finite supremum).
  obtain ⟨u, hu_max⟩ := Finite.exists_max
    (fun u : WordStack F (Fin 2) ι ↦
      if jointProximity C u δ then (0 : ENNReal)
      else Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ])
  have h_eps : epsCA (F := F) (A := F) C δ δ =
      (if jointProximity C u δ then (0 : ENNReal)
       else Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ]) := by
    refine le_antisymm ?_ ?_
    · rw [epsCA]; exact iSup_le hu_max
    · rw [epsCA]
      exact le_iSup (fun w : WordStack F (Fin 2) ι ↦
        if jointProximity C w δ then (0 : ENNReal)
        else Pr_{ let γ ← $ᵖ F }[δᵣ(w 0 + γ • w 1, C) ≤ δ]) u
  -- Positivity forces the maximiser to be *not* jointly close.
  have hjp : ¬ jointProximity C u δ := by
    intro h; rw [h_eps, if_pos h] at hca; exact lt_irrefl _ hca
  rw [if_neg hjp] at h_eps
  refine ⟨0, 0, 0, u 0, u 1, ?_, ?_⟩
  · -- Violation: `¬ R̃²`. Else relaxedRelation → jointAgreement → jointProximity.
    intro hrel
    apply hjp
    have hu_eq : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hu_eq, ← jointAgreement_iff_jointProximity]
    obtain ⟨Wstar, ⟨M, ⟨encode, hencC, hWstar⟩, _hconstr⟩, S, hScard, hSag⟩ := hrel
    refine ⟨S, ?_, Wstar, fun i ↦ ⟨hWstar i ▸ hencC (M i), ?_⟩⟩
    · -- card bound ℝ → ℝ≥0
      have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by rw [NNReal.coe_sub _hδ_lt.le]; simp
      rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_mul, e]
      push_cast
      linarith [hScard]
    · intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, (hSag i j hj).symm⟩
  · -- Cardinality bound: `S ⊆ Ω`, and `Pr·|F| = |S|`.
    rw [h_eps]
    have hsub : {γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ} ⊆ winningSet C δ 0 0 0 (u 0) (u 1) :=
      fun γ hγ ↦ mem_winningSet_zero_of_relClose _hδ_lt enc hC (u 0) (u 1) hγ
    have hF0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    have key : Pr_{ let γ ← $ᵖ F }[δᵣ(u 0 + γ • u 1, C) ≤ δ] * (Fintype.card F : ENNReal)
        = ({γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ}.ncard : ENNReal) := by
      rw [prob_uniform_eq_card_filter_div_card,
          Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      push_cast
      rw [ENNReal.div_mul_cancel (by exact_mod_cast hF0) (ENNReal.natCast_ne_top _)]
    rw [key]
    have hmono := Set.ncard_le_ncard hsub (Set.toFinite _)
    exact_mod_cast hmono

end ToyProblem
