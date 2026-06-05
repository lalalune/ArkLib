/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finite.GaloisField

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
common quantity** — the soundness error of the simplified IOR `T'[C]`
(Construction 6.9, the §6.4 attack target), `winningSetSoundness` — so the
scalar gap between them is meaningful:

* `SecurityLowerBound p` — an inhabitant is a proof "we can *prove* `≥ bits`
  bits of security": `soundnessError ≤ 2^(-bits)`. The proof routes through
  the full-protocol round-by-round (RBR) upper bound `toySoundnessError`
  (Lemmas 6.10 / 6.6 / 6.8).
* `SecurityUpperBound p` — an inhabitant is a proof "no analysis can prove
  `> bits` bits": `soundnessError ≥ 2^(-bits)`. The witness is the
  winning-set attack of Lemmas 6.12 / 6.13.
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) directly from the two inequalities, axiom-cleanly.

## The common quantity (central design decision)

The two sides **must** bound the same quantity or the gap is meaningless.
The trap: `toySoundnessError` (the full-protocol RBR max) is an *upper* bound,
while the attack lemmas L6.12/6.13 *lower* bound. So `attack ≤ error ≤
toySoundnessError`. We make the leaderboard quantity the **simplified-IOR
soundness error** `winningSetSoundness` — per `winningSet`'s Definition 6.11,
the worst-case winning-challenge fraction `|Ω|/|F|` over *violating* instances.
This is the object the §6.4 attacks directly lower-bound and Lemma 6.10
upper-bounds.

* the X side proves `soundnessError ≤ toySoundnessError ≤ 2^(-bits)`
  (`toySoundnessError` is the *vehicle*, not the leaderboard quantity);
* the Y side proves `soundnessError ≥ winningSet.ncard/|F| ≥ 2^(-bits)`.

**Why `winningSetSoundness` is `t`-independent (no `(1-δ)^t` term).** `T'[C]`
is single-round; its soundness error is *exactly* the winning fraction. The
spot-check term `(1-δ)^t` belongs to the *full* protocol C6.2, and at the
prize regime (`t=128`, `δ≈1-1/√2`) it equals `2^(-64)` — which alone exceeds
the attack target `2^(-116)`. Folding it into the common quantity would
collapse the attack side to a triviality (and, at a smaller `δ`, make the
provable side a *falsehood*). It therefore lives only in `toySoundnessError`,
where it correctly caps the *provable* security at 64 bits (ABF26 §6.3, `.tex`
2819–2823: the soundness is `max(2^(-71.5), 2^(-64))`, spot-check-dominated).

Stating the upper-bound structure against `soundnessError` (not
`toySoundnessError`) is what keeps the leaderboard faithful: a contestant
cannot "win" by inflating the RBR bound — they must exhibit a real attack.

The Phase-1 grand-challenge framework
(`ProximityGap.GrandChallenges`) feeds the X side: a tighter
`MCALowerWitness` shrinks the `ε_mca` term inside `toySoundnessError`, which
raises the provable lower bound `X`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2 Lemmas 6.6/6.8; §6.4 Lemmas 6.10, 6.12,
  6.13; Definition 6.11; §6.3 Tables 2–5).
* Fenzi, G., Sanso, A., *Small-field hash-based SNARGs are less sound than
  conjectured*, eprint 2025/2197 (Construction 4.2 ≈ C6.2; Lemma 4.4 is a
  similar observation to Lemma 6.12, per ABF26 §6.4.1).
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
side: an explicit attack witness lower-bounds `winningSetSoundness`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) :
    winningSetRatio x ≤ winningSetSoundness (k := k) C δ :=
  le_ciSup (bddAbove_winningSetRatio C δ) x

/-- **The correlated-agreement attack lower-bounds the simplified-IOR soundness**
(the §6.4.2 attack chain, end-to-end and machine-checked). For a linear code
`C`, the soundness error `winningSetSoundness` is at least the correlated
agreement error `ε_ca(C, δ)`. This is **Lemma 6.13 of [ABF26]**
(`simplified_iop_soundness_ca_lb`) packaged as a `ViolatingInstance` and pushed through
`winningSetRatio_le_winningSetSoundness`: the attack witness's winning fraction
`|Ω|/|F| ≥ ε_ca` is a genuine lower bound on the worst-case soundness.

This is the real content the §6.3-numeric attack anchors instantiate: a
`SecurityUpperBound` of `b` bits at a code with `ε_ca ≥ 2^(-b)` follows
immediately. Axiom-clean (no `sorryAx`); only the *numeric* `ε_ca ≥ 2^(-b)` at
the genuine KoalaBear code remains owed (Phase 5). -/
theorem epsCA_le_winningSetSoundness {k : ℕ} [Nonempty ι] (C : Set (ι → F)) (δ : ℝ≥0)
    (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C) :
    epsCA (F := F) (A := F) C δ δ ≤ (winningSetSoundness (k := k) C δ : ENNReal) := by
  rcases eq_or_lt_of_le (zero_le (epsCA (F := F) (A := F) C δ δ)) with h | hca
  · rw [← h]; exact zero_le _
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    simplified_iop_soundness_ca_lb C δ hδpos hδlt hClin hca
  set x : ViolatingInstance C δ k := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ with hx
  have hF0 : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hFt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hWReq : (winningSetRatio x : ENNReal)
      = ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal) / (Fintype.card F : ENNReal) := by
    rw [winningSetRatio, hx, ENNReal.coe_div (by simp [Fintype.card_ne_zero])]
    push_cast; rfl
  have hWR : (winningSetRatio x : ENNReal) ≤ (winningSetSoundness (k := k) C δ : ENNReal) := by
    exact_mod_cast winningSetRatio_le_winningSetSoundness x
  refine le_trans ?_ hWR
  rw [hWReq, ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
  exact hbound

/-! ## What the leaderboard quantity is, and is NOT

The common quantity is **`winningSetSoundness`** — the soundness error of the
*simplified IOR* `T'[C]` (Construction 6.9, the §6.4 attack target), per
Definition 6.11. This is the object the §6.4 attacks (Lemmas 6.12/6.13)
*directly* lower-bound and the §6.4 soundness analysis (Lemma 6.10) upper-bounds.

It is deliberately **t-independent**: `T'[C]` is single-round, so its soundness
error is exactly the worst-case winning fraction (no spot-check term). Folding a
`(1-δ)^t` term into this quantity would be unfaithful — it would (i) belong to
the *full* protocol C6.2, not C6.9, and (ii) at the prize regime `t = 128`,
`δ ≈ 1-1/√2`, the spot-check term is `(1/√2)^128 = 2^(-64)`, which alone
exceeds the attack target `2^(-116)` and dominates the provable target
`2^(-64)` — collapsing the attack side to a triviality and the provable side to
a falsehood. The `(1-δ)^t` round lives only in the X-side *vehicle*
`toySoundnessError` (the full-protocol RBR bound, below), where it correctly
caps the *provable* security at 64 bits (ABF26 §6.3, `.tex` lines 2819–2823:
the spot-check term dominates `max(2^(-71.5), 2^(-64))`). -/

/-! ## The RBR upper-bound vehicle (full protocol C6.2; Lemmas 6.6 / 6.8)

`toySoundnessError` reuses the *exact* per-round error terms of
`Spec.General.protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound`
(Lemmas 6.6 / 6.8): the `γ`-round error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and
the spot-check error `(1-δ)^t`. It upper-bounds `winningSetSoundness` (via
Lemma 6.10, since the `γ`-round error already dominates the simplified IOR's
error) and is the X-side vehicle. -/

/-- The round-by-round soundness upper bound of **Lemmas 6.6 / 6.8 of [ABF26]**
(the *full* protocol C6.2): the `max` of the combination-randomness error
`ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the spot-check error `(1-δ)^t`. These are
the *exact* per-round terms of `protocol62_knowledgeSound`. It bounds the
simplified-IOR soundness `winningSetSoundness` from above (X-side vehicle); the
`(1-δ)^t` branch is what caps provable security at 64 bits at the prize regime. -/
noncomputable def toySoundnessError (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max ((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0))
      ((1 - δ) ^ t)

/-
STATUS (DISPROVEN + NEEDS_CLASSICAL). This bound is the soundness analysis of
Construction 6.9 (ABF26 Lemma 6.10): `winningSetSoundness ≤ ε_mca + |Λ|/|F|`.
Its `ε_mca` term is the *mutual correlated agreement* error, whose provable
size hinges on the proximity radius `δ` one is allowed to take. The
up-to-capacity reading (correlated-agreement / mutual-correlated-agreement /
list-decodability with `BStar = ρ`) was DISPROVEN in 2025 (Crites–Stewart;
Ben-Sasson–Carmon–Haback–Kopparty–Saraf; Diamond–Gruen;
eprint.iacr.org/2025/2046): it is FALSE for some Reed–Solomon families, so any
sorry discharged at capacity would be discharging a false statement. The
provable replacement is the Johnson-radius variant (`BStar = √ρ`). Even the
Johnson-radius bound is NEEDS_CLASSICAL: discharging it requires classical
coding-theory results (Johnson bound / Guruswami–Sudan / Reed–Solomon
list-decoding) that are NOT yet in mathlib (no Reed–Solomon, list-decoding, or
Johnson API upstream) — a genuine ground-up formalization, not a port. Do not
attempt to close the sorry; do not remove it. See
research/formal/arklib-proof-research-2026-06.md.
-/
/-- **The simplified-IOR soundness is below the full-protocol RBR bound**
(**Lemma 6.10 of [ABF26]**). `winningSetSoundness ≤ toySoundnessError`: the
simplified IOR's worst-case winning fraction is at most the `γ`-round error
`ε_mca + |Λ|/|F|` (Lemma 6.10 — the soundness of Construction 6.9), which is the
first branch of the `max`. The X side routes through this to turn an
`ε_mca`/`Λ` bound (and the `(1-δ)^t` spot-check cap) into a provable security
lower bound. -/
theorem winningSetSoundness_le_toySoundnessError {k : ℕ}
    (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) :
    winningSetSoundness (k := k) C δ ≤ toySoundnessError C δ t := by
  refine le_trans ?_ (le_max_left _ _)
  -- tagged sorry [ABF26 Lemma 6.10, §6.4] — `winningSetSoundness ≤ ε_mca + |Λ|/|F|`
  -- is the soundness of Construction 6.9 (the 1-round form of the L6.8 γ-round);
  -- paper-proof-owed (ABF26's own §6.4 result).
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
  /-- Documentary: intended block length `n` (the intended rate is `ρ = k/n`).
  Need not equal `|ι|` for stand-in parameters. -/
  n : ℕ := 0
  /-- Documentary: Johnson slack `η`. -/
  η : ℝ≥0 := 0

attribute [instance] ToyParams.field ToyParams.fintypeF ToyParams.decEqF ToyParams.fintypeι

/-- The leaderboard's common quantity at a parameter point: the simplified-IOR
(Construction 6.9 / Definition 6.11) soundness error `winningSetSoundness`,
projected onto the bundled carrier. -/
noncomputable def ToyParams.soundnessError (p : ToyParams) : ℝ≥0 :=
  winningSetSoundness (k := p.k) p.C p.δ

/-- The full-protocol RBR upper-bound vehicle (Lemmas 6.6 / 6.8) at a parameter
point. -/
noncomputable def ToyParams.toySoundnessError (p : ToyParams) : ℝ≥0 :=
  _root_.ToyProblem.toySoundnessError p.C p.δ p.t

/-- `soundnessError ≤ toySoundnessError` at a parameter point (Lemma 6.10). -/
theorem ToyParams.soundnessError_le_toySoundnessError (p : ToyParams) :
    p.soundnessError ≤ p.toySoundnessError :=
  _root_.ToyProblem.winningSetSoundness_le_toySoundnessError (k := p.k) p.C p.δ p.t

/-! ## The two leaderboard interfaces

Both are stated against the **same** common quantity `p.soundnessError`. A
submission is an *inhabitant*. -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the simplified-IOR soundness error is `≤ 2^(-bits)` — i.e. "we
can *prove* at least `bits` bits of security." The intended proof route is
`soundnessError ≤ toySoundnessError ≤ 2^(-bits)` via [ABF26] Lemmas 6.10 / 6.6.
`bits : ℝ` because the security level *is* `bitsOfSecurity e = -log₂ e`, a real for
any soundness error `e ∈ (0,1)` (almost never an integer); the §6.3 figures the
anchors quote are themselves fractional (the attack is `2^(-116.49)`, the C6.9 MCA
branch `≈ 2^(-71.5)`, the spot-check `(1-δ)^128 ≈ 2^(-65.9)`). -/
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
sextic extension, `ρ = 1/2`, `t = 128`). Two design points keep the anchors
*honest* (no `sorry` hiding a provably-false goal):

1. **The carrier field is large.** The soundness error is a fraction `|Ω|/|F|`,
   so to even *represent* a value in the target window `[2^(-116), 2^(-64)]` the
   field must satisfy `|F| ≥ 2^116`. We use `GaloisField 2 128` (size `2^128`) —
   a stand-in of the right *order* for the genuine KoalaBear-sextic field (size
   `≈2^186`), which Phase 5 substitutes. (Over a tiny field like `𝔽₂`, `|Ω|/|F|`
   lives in `{0, 1/2, 1}` and the two anchors would be *jointly* unsatisfiable.)
2. **The code is opaque.** `koalaCode`'s fine structure is hidden, so
   `winningSetSoundness koalaIRS` is irreducible — neither anchor's inequality is
   provably true *or* false; they are genuine owed obligations (Phase 3 supplies
   the §6 proofs, Phase 5 the genuine RS/IRS code and numerics). `opaque` is
   axiom-clean (no `sorryAx`).

The two anchors below are `sorry`-backed by design (like Phase 1's
`MCALowerWitness.ofJohnsonBCHKS25`). -/

/-- `𝔽₂` primality, for the `GaloisField 2 128` anchor carrier. Kept `local`
so it does not leak `Fact (Nat.Prime 2)` into downstream importers. -/
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Opaque placeholder code over the KoalaBear-sextic-sized field `GF(2^128)`;
its fine structure is deferred to Phase 5 (the genuine RS/IRS code). Keeping it
`opaque` makes `winningSetSoundness koalaIRS` irreducible, so the anchor
inequalities are genuine owed obligations rather than computable (and hence
provably true/false) at this stand-in. -/
opaque koalaCode : Set (Fin 3 → GaloisField 2 128)

/-- The Proximity-Prize anchor parameter point: the KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`). The proximity
radius is set near capacity, `δ = 3/10` (just above `1 - 1/√2 ≈ 0.293`), so the
full-protocol spot-check term `(1-δ)^128 ≈ 2^(-65.9) ≤ 2^(-64)` is consistent
with the headline 64-bit provable ceiling (cf. ABF26 §6.3, `.tex` 2819–2823).
The carrier is the `2^128`-element field `GaloisField 2 128` (a same-order
stand-in for the `≈2^186`-element KoalaBear sextic; Phase 5 substitutes the
real field and code). The documentary numeric fields `(q, ext, ρ, s, n, η)`
state the *intended* KoalaBear-sextic regime (rate `ρ = k/n = 2/4 = 1/2`); the
operational stand-in `(F = GF(2^128), ι = Fin 3, k = 2, opaque C)` does not yet
realise it (it is not literally a rate-`1/2` RS code over the sextic field) —
Phase 5 reconciles the two. -/
noncomputable def koalaIRS : ToyParams := by
  haveI : Fintype (GaloisField 2 128) := Fintype.ofFinite _
  classical
  exact
    { F := GaloisField 2 128
      ι := Fin 3
      C := koalaCode
      δ := 3 / 10
      t := 128
      k := 2
      q := 2 ^ 31 - 2 ^ 24 + 1
      ext := 6
      ρ := 1 / 2
      s := 1
      n := 4
      η := 1 / 16 }

/-
STATUS (OPEN_PRIZE). This anchor is the *provable-security* (X) side of the
EF Proximity Prize / ABF26 §6 Grand Challenge: how many bits of soundness can
one actually *prove* for the toy protocol at the KoalaBear-sextic rate regime
(target `ε* = 2^-128` at rates `1/2 .. 1/16`). Maximising this provable `bits`
is the open research problem the prize poses — it is an unsolved research
problem, not a closeable Lean obligation. The `64`-bit value here is a
placeholder anchor, and the proof route moreover inherits the
DISPROVEN/NEEDS_CLASSICAL status of `winningSetSoundness_le_toySoundnessError`
(the up-to-capacity `ε_mca` term, disproven 2025; the Johnson-radius
replacement needs absent mathlib coding-theory API). Do not attempt to close
the sorry; do not remove it. See
research/formal/arklib-proof-research-2026-06.md.
-/
/-- **ArkLib provable lower bound (≈64 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemmas 6.10 / 6.6 / 6.8 of [ABF26]**: the simplified-IOR
soundness error is bounded by the full-protocol RBR error
`max (ε_mca + |Λ|/|F|) ((1-δ)^t)`, which evaluates to ≈`2^(-64)` at the §6.3
Table 2–3 numerics — the spot-check branch `(1-δ)^128 = (1/√2)^128 = 2^(-64)`
is the binding cap (`.tex` 2819–2823; the `ε_mca + |Λ|/|F|` branch is the even
tighter ≈`2^(-71.5)`). 64 is thus a *conservative* (improvable) provable bound on
`winningSetSoundness`. The proof routes `soundnessError ≤ toySoundnessError ≤
2^(-64)`. `sorry`-backed (the §6.3 numeric evaluation is Phase 5). -/
noncomputable def arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS where
  bits := 64
  proof := by
    -- ABF26-L6.10/L6.6 + §6.3 Tables 2–3; paper-proof-owed. The route is
    -- `soundnessError ≤ toySoundnessError` (L6.10, already a lemma) followed by
    -- the Phase-5 numeric check `toySoundnessError ≤ 2^(-64)` (its spot-check
    -- branch `(1-δ)^128 ≈ 2^(-65.9) ≤ 2^(-64)` at `δ = 3/10`). Tagged sorry.
    refine le_trans koalaIRS.soundnessError_le_toySoundnessError ?_
    -- tagged sorry [ABF26 §6.3 Tables 2–3] — Phase-5 numeric check.
    sorry

/-- **Winning-set attack upper bound (≈116 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1; a similar observation appears
in Fenzi–Sanso, eprint 2025/2197, Lemma 4.4): the winning challenge set is large
enough that, at KoalaBear-sextic `ρ=1/2, t=128`, the simplified-IOR soundness
error is `≥ ≈2^(-116)` (ABF26 §6.3, `.tex` 2925: `2^(-116.49)`). The witness is
the attack instance, lower-bounding `winningSetSoundness` directly via
`winningSetRatio_le_winningSetSoundness`. `sorry`-backed (L6.12 carries the
side-hyp `|F| > C(N,2)`; the numeric ≈116 and the witness-violation packaging
are Phase 5 / Phase 3). -/
noncomputable def fenziSanso_upperBound_attack : SecurityUpperBound koalaIRS where
  bits := 116
  proof := by
    -- ABF26-L6.12/6.13 (cf. Fenzi–Sanso 2025/2197 Lemma 4.4). The attack→soundness
    -- chain is now REAL and axiom-clean: `epsCA_le_winningSetSoundness` proves
    -- `ε_ca(C,δ) ≤ winningSetSoundness C δ` end-to-end (L6.13 packaged as a
    -- `ViolatingInstance`, with its violation certified, through
    -- `winningSetRatio_le_winningSetSoundness`). All that remains owed here is the
    -- *numeric* `2^(-116) ≤ ε_ca koalaCode (3/10)` (the §6.3 Table evaluation,
    -- `.tex` 2925: `2^(-116.49)`) together with `koalaCode`'s linearity — both
    -- deferred to Phase 5, where the opaque `koalaCode` is replaced by the genuine
    -- linear KoalaBear-sextic RS/IRS code. With those in hand the proof is
    -- `le_trans (numeric bound) (epsCA_le_winningSetSoundness …)`. Tagged sorry.
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
