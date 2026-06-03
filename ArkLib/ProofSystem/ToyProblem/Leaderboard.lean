/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Field.ZMod

/-!
# Proximity-Prize "bits of security" leaderboard (ABF26 §6)

A machine-checked **leaderboard contract** for the soundness of the §6 toy
protocol (Construction 6.2 / its simplified IOR Construction 6.9). The
Ethereum Foundation Proximity Prize (proximityprize.org) asks for the gap
between the *provable* security of small-field hash-based SNARGs and the
*best known attack*; at the KoalaBear-sextic regime (`ρ = 1/2`, `t = 128`)
this is the ≈64-vs-≈116-bit frontier (ABF26 §6.3 Tables 2–5, and the
standalone attack of Fenzi–Sanso, eprint 2025/2197).

This file states that frontier as two opposing Lean structures over **one
common quantity** — the protocol's *actual* soundness error — so the scalar
gap between them is meaningful:

* `SecurityLowerBound p` — an inhabitant is a proof "we can *prove* `≥ bits`
  bits of security": `soundnessError ≤ 2^(-bits)`. The proof routes through
  the round-by-round (RBR) upper bound `toySoundnessError` (Lemma 6.8).
* `SecurityUpperBound p` — an inhabitant is a proof "no analysis can prove
  `> bits` bits": `soundnessError ≥ 2^(-bits)`. The witness is the
  winning-set attack of Lemmas 6.12 / 6.13.
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) directly from the two inequalities, axiom-cleanly.

## The common quantity (central design decision)

The two sides **must** bound the same quantity or the gap is meaningless.
The trap: `toySoundnessError` (the L6.8 RBR per-round max) is an *upper*
bound on the true soundness error, while the attack lemmas L6.12/6.13 *lower*
bound it. So `attack ≤ trueError ≤ toySoundnessError`. We therefore make the
leaderboard quantity the protocol's **actual soundness error**
`soundnessError`, defined (per `winningSet`'s Definition 6.11 docstring) as
the worst-case winning-challenge fraction over violating instances, combined
with the spot-check round error `(1-δ)^t`:

* the X side proves `soundnessError ≤ toySoundnessError ≤ 2^(-bits)`
  (`toySoundnessError` is the *vehicle*, not the leaderboard quantity);
* the Y side proves `soundnessError ≥ winningSet.ncard/|F| ≥ 2^(-bits)`.

Stating the upper-bound structure against `soundnessError` (not
`toySoundnessError`) is what keeps the leaderboard faithful: a contestant
cannot "win" by inflating the RBR bound — they must exhibit a real attack.

The Phase-1 grand-challenge framework
(`ProximityGap.GrandChallenges`) feeds the X side: a tighter
`MCALowerWitness` shrinks the `ε_mca` term inside `toySoundnessError`, which
raises the provable lower bound `X`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2 Lemma 6.8; §6.4 Lemmas 6.12, 6.13;
  §6.3 Tables 2–5).
* Fenzi, G., Sanso, A., *Small-field hash-based SNARGs are less sound than
  conjectured*, eprint 2025/2197 (Construction 4.2 = C6.2, Lemma 4.4 = L6.12).
-/

-- Several plumbing lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide,
-- matching the idiom in `ProximityGap/GrandChallenges.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-! ## The soundness scalar (Definition 6.11 reading)

`winningSetSoundness` is the simplified IOR's actual soundness error: the
supremum, over instances `(v, μ₁, μ₂, f₁, f₂)` that *violate* the relaxed
relation `R̃_{C,δ}^2`, of the winning-challenge fraction `|Ω| / |F|`. The
violating constraint is essential — over *all* inputs a valid instance has
`Ω = F` (fraction `1`), so the unrestricted sup is the trivial `1`. -/

/-- An instance of the simplified IOR whose stack `(v, μ₁, μ₂, f₁, f₂)`
violates the relaxed relation `R̃_{C,δ}^2`. This is the index of the
worst-case soundness supremum of Definition 6.11. -/
structure ViolatingInstance (C : Set (ι → F)) (δ : ℝ≥0) (k : ℕ) where
  /-- The linear-constraint vector. -/
  v : Fin k → F
  /-- First constraint value. -/
  μ₁ : F
  /-- Second constraint value. -/
  μ₂ : F
  /-- First input word. -/
  f₁ : ι → F
  /-- Second input word. -/
  f₂ : ι → F
  /-- The instance violates the relaxed two-row relation `R̃_{C,δ}^2`. -/
  violates : ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂]

/-- The winning-challenge fraction `|Ω^{f₁,f₂}_{v,μ₁,μ₂}| / |F|` of a
violating instance. Always in `[0, 1]` (`winningSet ⊆ F`). -/
noncomputable def winningSetRatio {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) : ℝ≥0 :=
  ((winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Definition 6.11 of [ABF26]** (soundness error of the simplified IOR).

The worst-case winning-challenge fraction over violating instances:
`sup_{(v,μ₁,μ₂,f₁,f₂) violating R̃²} |Ω| / |F|`. This is the protocol's
*actual* soundness error after the combination-randomness round — the common
quantity the leaderboard's two sides bound from opposite directions. -/
noncomputable def winningSetSoundness {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance C δ k, winningSetRatio x

/-- The winning-challenge fraction never exceeds `1` (`winningSet ⊆ F`). -/
theorem winningSetRatio_le_one {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) : winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [winningSetRatio, div_le_one hpos]
  have hle : (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ Fintype.card F := by
    have := Set.ncard_le_ncard (Set.subset_univ
      (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂)) (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  exact_mod_cast hle

/-- The family of winning-challenge fractions is bounded above (by `1`), so
its supremum is well-behaved in the conditionally complete order `ℝ≥0`. -/
theorem bddAbove_winningSetRatio {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ViolatingInstance C δ k ↦ winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, rfl⟩
  exact winningSetRatio_le_one x

/-- Each violating instance's winning fraction is a lower bound on the
soundness error of [ABF26] Definition 6.11 — the backbone of the attack (Y)
side: an explicit attack witness lower-bounds `winningSetSoundness`, hence
`soundnessError`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) :
    winningSetRatio x ≤ winningSetSoundness (k := k) C δ :=
  le_ciSup (bddAbove_winningSetRatio C δ) x

/-- The protocol's **actual soundness error**: the worse of the
combination-randomness round (`winningSetSoundness`, Definition 6.11) and the
spot-check round `(1-δ)^t`. This is the leaderboard's common quantity; the two
sides bound it from opposite directions. -/
noncomputable def soundnessError {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max (winningSetSoundness (k := k) C δ) ((1 - δ) ^ t)

/-! ## The RBR upper-bound vehicle (Lemma 6.8)

`toySoundnessError` reuses the *exact* per-round error terms of
`Spec.General.protocol62_rbrKnowledgeSound` (Lemma 6.8): the `γ`-round error
`ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the spot-check error `(1-δ)^t`. It is
the X-side vehicle — an upper bound on `soundnessError`, **not** the
leaderboard quantity. -/

/-- The round-by-round soundness upper bound of **Lemma 6.8 of [ABF26]**: the
`max` of the combination-randomness error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|`
and the spot-check error `(1-δ)^t`. These are the *exact* per-round terms of
`protocol62_rbrKnowledgeSound`; this is the X-side vehicle, an upper bound on
`soundnessError`. -/
noncomputable def toySoundnessError (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max ((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0))
      ((1 - δ) ^ t)

/-- **RBR soundness direction (Lemma 6.8 of [ABF26]).** The actual soundness
error is bounded by the round-by-round vehicle: `soundnessError ≤
toySoundnessError`. The spot-check terms coincide, so this reduces to the
`γ`-round content of L6.8 — `winningSetSoundness ≤ ε_mca + |Λ|/|F|` — i.e.
that the worst-case winning fraction is bounded by the MCA + list-decoding
error. The X side routes through this to turn an `ε_mca`/`Λ` bound into a
provable security lower bound. -/
theorem soundnessError_le_toySoundnessError {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) :
    soundnessError (k := k) C δ t ≤ toySoundnessError C δ t := by
  -- ABF26-L6.8; paper-proof-owed [ABF26 Lemma 6.8, §6.2]. Reduces (the
  -- spot-check terms being identical) to the γ-round RBR bound
  -- `winningSetSoundness ≤ ε_mca + |Λ|/|F|`, which is exactly the content of
  -- `protocol62_rbrKnowledgeSound` at round 0. Tagged sorry.
  refine max_le_max ?_ (le_refl _)
  -- tagged sorry [ABF26 Lemma 6.8] — the γ-round RBR bound, paper-proof-owed.
  sorry

/-! ## Bits of security -/

/-- Provable security in bits of a soundness error `e`: `-log₂ e`. At `e = 0`
(perfect soundness) `Real.logb 2 0 = 0`, so `bitsOfSecurity 0 = 0`; callers
exhibiting genuine perfect soundness should special-case it. For the prize
regime `e ∈ (0, 1)` so `bitsOfSecurity e > 0`. -/
noncomputable def bitsOfSecurity (e : ℝ≥0) : ℝ := -Real.logb 2 (e : ℝ)

/-! ## Parameter record (KoalaBear-sextic regime)

`ToyParams` bundles the ambient field/index and interpreted code (the
universe-pinned bridge — `epsMCA`/`Λ` need their code at `Type 0`) together
with the plain-data numeric regime (KoalaBear field size `q`, sextic
extension, rate `ρ`, and `s, n, k, t, δ, η`). Full numeric population — and
swapping the placeholder code for the genuine KoalaBear-sextic RS/IRS code —
is Phase 5. -/

/-- The KoalaBear-sextic parameter regime plus its code interpretation. The
operational fields `(F, ι, C, δ, t, k)` feed `soundnessError`; the documentary
fields `(q, ext, ρ, s, n, η)` record the §6.3 numeric regime for Phase 5 and
the wiki. All carrier types are pinned to `Type 0`. -/
structure ToyParams where
  /-- Ambient field (`Type 0`; KoalaBear sextic at Phase 5). -/
  F : Type
  /-- Codeword index type (`Type 0`; `Fin n`). -/
  ι : Type
  [field : Field F]
  [fintypeF : Fintype F]
  [decEqF : DecidableEq F]
  [fintypeι : Fintype ι]
  /-- The interpreted base code `C ⊆ (ι → F)`. -/
  C : Set (ι → F)
  /-- Proximity radius `δ`. -/
  δ : ℝ≥0
  /-- Number of spot-check repetitions `t`. -/
  t : ℕ
  /-- Constraint dimension `k` (gives `winningSet`'s `v : Fin k → F`). -/
  k : ℕ
  /-- Documentary: field characteristic-prime size `q` (KoalaBear: `2^31 - 2^24 + 1`). -/
  q : ℕ := 2 ^ 31 - 2 ^ 24 + 1
  /-- Documentary: extension degree (KoalaBear sextic: `6`). -/
  ext : ℕ := 6
  /-- Documentary: rate `ρ = k/n` (prize regime `1/2`). -/
  ρ : ℝ≥0 := 1 / 2
  /-- Documentary: interleaving / codeword symbol size `s`. -/
  s : ℕ := 1
  /-- Documentary: block length `n = |ι|`. -/
  n : ℕ := 0
  /-- Documentary: Johnson slack `η`. -/
  η : ℝ≥0 := 0

attribute [instance] ToyParams.field ToyParams.fintypeF ToyParams.decEqF ToyParams.fintypeι

/-- The actual soundness error at a parameter point — the leaderboard's common
quantity, projected onto the bundled carrier. -/
noncomputable def ToyParams.soundnessError (p : ToyParams) : ℝ≥0 :=
  _root_.ToyProblem.soundnessError (k := p.k) p.C p.δ p.t

/-- The RBR upper-bound vehicle (Lemma 6.8) at a parameter point. -/
noncomputable def ToyParams.toySoundnessError (p : ToyParams) : ℝ≥0 :=
  _root_.ToyProblem.toySoundnessError p.C p.δ p.t

/-- `soundnessError ≤ toySoundnessError` at a parameter point (Lemma 6.8). -/
theorem ToyParams.soundnessError_le_toySoundnessError (p : ToyParams) :
    p.soundnessError ≤ p.toySoundnessError :=
  _root_.ToyProblem.soundnessError_le_toySoundnessError (k := p.k) p.C p.δ p.t

/-! ## The two leaderboard interfaces

Both are stated against the **same** common quantity `p.soundnessError`. A
submission is an *inhabitant*. -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the actual soundness error is `≤ 2^(-bits)` — i.e. "we can
*prove* at least `bits` bits of security." The intended proof route is
`soundnessError ≤ toySoundnessError ≤ 2^(-bits)` via [ABF26] Lemma 6.8.
`bits : ℝ` so fractional bits (e.g. `116.5`) are representable. -/
structure SecurityLowerBound (p : ToyParams) where
  /-- The provable security level, in bits. -/
  bits : ℝ
  /-- The actual soundness error is at most `2^(-bits)`. -/
  proof : p.soundnessError ≤ (2 : ℝ≥0) ^ (-bits)

/-- **Provable security upper bound** at parameter point `p`: a number `bits`
and a proof that the actual soundness error is `≥ 2^(-bits)` — i.e. "no
analysis can prove *more* than `bits` bits of security." The witness is the
winning-set attack of [ABF26] Lemmas 6.12 / 6.13: `soundnessError ≥ |Ω|/|F| ≥
2^(-bits)`. -/
structure SecurityUpperBound (p : ToyParams) where
  /-- The provable security ceiling, in bits. -/
  bits : ℝ
  /-- The actual soundness error is at least `2^(-bits)`. -/
  proof : p.soundnessError ≥ (2 : ℝ≥0) ^ (-bits)

/-! ## The leaderboard metric -/

/-- **The leaderboard metric.** The scalar gap `Y − X` between the best known
attack (`hi`) and the best provable security (`lo`). Contestants minimise this
— at the KoalaBear-sextic regime it is the ≈116 − 64 = 52-bit frontier. -/
def securityGap {p : ToyParams} (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ :=
  hi.bits - lo.bits

/-- **The [ABF26] §6 prize gap is honest** (`lo.bits ≤ hi.bits`, so
`securityGap ≥ 0`). Proved
directly from the two inequalities: `2^(-hi.bits) ≤ soundnessError ≤
2^(-lo.bits)`, and `x ↦ 2^(-x)` is strictly antitone, so `lo.bits ≤ hi.bits`.
No degenerate `error = 0` case arises: the two `2^(-·)` terms are positive and
are chained transitively, never divided by the error. Axiom-clean. -/
theorem SecurityLowerBound.bits_le_of {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    lo.bits ≤ hi.bits := by
  -- `2^(-hi.bits) ≤ soundnessError ≤ 2^(-lo.bits)` in `ℝ≥0`.
  have hchain : (2 : ℝ≥0) ^ (-hi.bits) ≤ (2 : ℝ≥0) ^ (-lo.bits) :=
    le_trans hi.proof lo.proof
  -- Cast to `ℝ` and use strict monotonicity of `2^(·)`.
  have hchainR : (2 : ℝ) ^ (-hi.bits) ≤ (2 : ℝ) ^ (-lo.bits) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_ofNat] at this
  have hexp : -hi.bits ≤ -lo.bits :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hchainR
  linarith

/-- `securityGap` is non-negative. -/
theorem securityGap_nonneg {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    0 ≤ securityGap lo hi := by
  have := lo.bits_le_of hi
  simp only [securityGap]; linarith

/-! ### The `bits` interpretation

A `SecurityLowerBound`/`SecurityUpperBound` `bits` field is exactly a bound on
the true bits-of-security `bitsOfSecurity soundnessError`. Together these read:
`lo.bits ≤ bitsOfSecurity (soundnessError) ≤ hi.bits` (when the error is
positive), i.e. the certified provable level sits below the true level, which
sits below the attack ceiling. -/

/-- A provable lower bound's `bits` is at most the true bits-of-security
(equivalently to `lo.proof`, when the soundness error is positive). -/
theorem SecurityLowerBound.le_bitsOfSecurity {p : ToyParams} (lo : SecurityLowerBound p)
    (h : 0 < p.soundnessError) : lo.bits ≤ bitsOfSecurity p.soundnessError := by
  rw [bitsOfSecurity, le_neg, Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr lo.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-- A provable upper bound's `bits` is at least the true bits-of-security
(equivalently to `hi.proof`, when the soundness error is positive). -/
theorem SecurityUpperBound.bitsOfSecurity_le {p : ToyParams} (hi : SecurityUpperBound p)
    (h : 0 < p.soundnessError) : bitsOfSecurity p.soundnessError ≤ hi.bits := by
  rw [bitsOfSecurity, neg_le, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr hi.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-! ## Anchor parameter point and the two current entries

`koalaIRS` fixes the KoalaBear-sextic regime numerics (`q = 2^31 - 2^24 + 1`,
sextic extension, `ρ = 1/2`, `t = 128`). Its *code interpretation* is, for now,
a small genuine linear stand-in (a parity code over `ZMod 2`); the genuine
KoalaBear-sextic RS/IRS code is Phase 5. The two anchors below are
`sorry`-backed by design (like Phase 1's `MCALowerWitness.ofJohnsonBCHKS25`) —
the soundness *inequalities* are real propositions; only their §6 proofs and
Phase-5 numerics are owed. -/

/-- The Proximity-Prize anchor parameter point: the KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`). The code
interpretation is a small parity stand-in pending the Phase-5 RS/IRS
instantiation; the documentary numeric fields carry the genuine regime. -/
noncomputable def koalaIRS : ToyParams := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    { F := ZMod 2
      ι := Fin 3
      C := {w | ∑ i, w i = 0}
      δ := 1 / 4
      t := 128
      k := 2
      q := 2 ^ 31 - 2 ^ 24 + 1
      ext := 6
      ρ := 1 / 2
      s := 1
      n := 3
      η := 1 / 16 }

/-- **ArkLib provable lower bound (≈64 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.8 of [ABF26]** (§6.2): the RBR soundness error
`max (ε_mca + |Λ|/|F|) ((1-δ)^t)` evaluates to ≈`2^(-64)` at the §6.3 Table 2–3
numerics. The proof routes `soundnessError ≤ toySoundnessError ≤ 2^(-64)`.
`sorry`-backed (the §6.3 numeric evaluation is Phase 5). -/
noncomputable def arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS where
  bits := 64
  proof := by
    -- ABF26-L6.8 + §6.3 Tables 2–3; paper-proof-owed. The route is
    -- `soundnessError ≤ toySoundnessError` (L6.8, already a lemma) followed by
    -- the Phase-5 numeric check `toySoundnessError ≤ 2^(-64)`. Tagged sorry.
    refine le_trans koalaIRS.soundnessError_le_toySoundnessError ?_
    -- tagged sorry [ABF26 Lemma 6.8 + §6.3 Tables 2–3] — Phase-5 numeric check.
    sorry

/-- **Fenzi–Sanso attack upper bound (≈116 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1) = **Lemma 4.4 of
Fenzi–Sanso, eprint 2025/2197**: the winning set has size
`≥ N·|F|/(|F|+N−1)` (`N := |Λ(C^{≡2},δ)|`), which at KoalaBear-sextic `ρ=1/2,
t=128` lower-bounds the soundness error by ≈`2^(-116)`. The witness is the
attack instance: `soundnessError ≥ winningSetSoundness ≥ |Ω|/|F| ≥ 2^(-116)`
(via `winningSetRatio_le_winningSetSoundness`). `sorry`-backed (L6.12 carries
the side-hyp `|F| > C(N,2)`; the numeric ≈116 and the witness-violation step
are Phase 5 / Phase 3). -/
noncomputable def fenziSanso_upperBound_attack : SecurityUpperBound koalaIRS where
  bits := 116
  proof := by
    -- ABF26-L6.12 / Fenzi–Sanso 2025/2197 Lemma 4.4; paper-proof-owed. Route:
    -- extract the attack witness from `simplified_iop_soundness_listDecoding_lb`,
    -- package it as a `ViolatingInstance`, then chain
    -- `winningSetRatio_le_winningSetSoundness` (≤ soundnessError via `le_max_left`)
    -- with the Phase-5 numeric `|Ω|/|F| ≥ 2^(-116)`. Tagged sorry.
    sorry

/-- **The current leaderboard frontier.** At the KoalaBear-sextic anchor the
provable security is ≈64 bits and the best known attack is ≈116 bits, so the
gap the prize asks contestants to close is `116 − 64 = 52` bits (see [ABF26]
§6.3 Tables 2–5). The value is a
pure arithmetic readoff of the two `bits` fields — it does not depend on the
anchors' owed §6 *proofs* being correct (though, naming the anchor defs, this
lemma inherits their tagged `sorry`; the metric lemma `bits_le_of` is the
anchor-independent, axiom-clean guarantee). -/
theorem securityGap_koalaIRS_anchors :
    securityGap arklib_lowerBound_irs_t128 fenziSanso_upperBound_attack = 52 := by
  simp only [securityGap, arklib_lowerBound_irs_t128, fenziSanso_upperBound_attack]
  norm_num

end ToyProblem
