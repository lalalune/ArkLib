/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRefutation
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The concrete rank-deficient RIM instance for the μ_{2^t} derandomization refutation

`MuTwoPowDerandRefutation` refutes the μ_{2^t} derandomization property at the *certificate*
level: the ±-pair hypergraph `badHypergraph` is 3-weakly-partition-connected yet admits a
nonzero degree-`< 3` agreement certificate at the geometric point `Xᵢ = ω^i` whenever
`ω⁴ = -1`.  This file completes the picture at the *matrix* level, which is the form in
which the AGL24/Guo–Zhang capacity machinery actually consumes the property: it defines the
concrete reduced intersection matrix (RIM) of `badHypergraph` at the geometric point and
proves the determinant/rank drop.

## The matrix

Following the standard RIM convention (BGM23/AGL24), the reference vertex `2` is dropped;
columns `0–2` carry the monomial coefficients `1, X, X²` of the polynomial at vertex `0`,
and columns `3–5` those of vertex `1`.  Each two-element edge `{u, v}` at coordinate `i`
contributes one row expressing `p_u(ω^i) - p_v(ω^i) = 0`: the row is `(1, ω^i, ω^{2i})` on
the block of `u` and the negation on the block of `v` (nothing on the dropped reference).
The six nonempty edges of `badHypergraph` sit at coordinates `0, 1, 2, 4, 5, 6`, giving a
square 6×6 matrix `rim ω`.

## Main results

* `MuTwoPowDerandRefutation.rim` — the concrete 6×6 RIM at the geometric point.
* `MuTwoPowDerandRefutation.rimKernelVec` — the explicit kernel vector: the coefficient
  vector of the certificate `(p₀, p₁)` (see `rimKernelVec_poly₀`/`rimKernelVec_poly₁`).
* `MuTwoPowDerandRefutation.rim_mulVec_eq_certDiff` — the formal kernel ↔ certificate
  bridge: row `r` of `rim ω *ᵥ rimKernelVec ω` *is* the certificate evaluation difference
  across the edge at coordinate `coord r` (an identity in `ω`, no hypothesis needed).
* `MuTwoPowDerandRefutation.rim_det_eq_zero` — `det (rim ω) = 0` whenever `ω⁴ = -1`.
* `MuTwoPowDerandRefutation.rim_rank_lt_six` — the column-rank drop `rank (rim ω) < 6`.
* `MuTwoPowDerandRefutation.rim_rank_drop` — the packaged refutation: a 3-wpc hypergraph
  whose RIM at the geometric point is singular and column-rank-deficient.
* `MuTwoPowDerandRefutation.rim_zmod17_eq`, `rim_det_eq_zero_zmod17`,
  `rim_rank_lt_six_zmod17`, `rimKernelVec_zmod17_eq` — the fully concrete first
  certificate over the prize-shaped prime field `F₁₇` (`ω = 9`, of order 8), matching the
  mod-`p` computation in `research/proximity-prize/conj3-proof/pmpair_counterexample.py`
  (kernel vector `(5, 0, 14, 1, 0, 1)`).

The symbolic determinant over `ℤ[q]` is
`D(q) = q⁸ (q-1)⁶ (q+1)⁴ Φ₄(q)³ Φ₈(q)`; the `Φ₈` factor is exactly what
`rim_det_eq_zero` witnesses at any `ω` with `ω⁴ = -1`. -/

namespace MuTwoPowDerandRefutation

open Polynomial Finset

variable {F : Type*} [Field F] (ω : F)

/-- The reduced intersection matrix of `badHypergraph` at the geometric point
`Xᵢ = ω^i`.  Rows correspond to the nonempty edges at coordinates `0, 1, 2, 4, 5, 6`
(see `coord`); columns `0–2` are the coefficient block of vertex `0`, columns `3–5` the
block of vertex `1`, and the reference vertex `2` is dropped. -/
def rim : Matrix (Fin 6) (Fin 6) F :=
  !![1, 1, 1, -1, -1, -1;
     1, ω, ω ^ 2, 0, 0, 0;
     0, 0, 0, 1, ω ^ 2, ω ^ 4;
     1, ω ^ 4, ω ^ 8, -1, -ω ^ 4, -ω ^ 8;
     1, ω ^ 5, ω ^ 10, 0, 0, 0;
     0, 0, 0, 1, ω ^ 6, ω ^ 12]

/-- The kernel certificate vector: columns `0–2` hold the coefficients of
`p₀ = (1 + ω²)·(X² - ω²)` and columns `3–5` those of `p₁ = X² + 1`. -/
def rimKernelVec : Fin 6 → F :=
  ![-(ω ^ 2) * (1 + ω ^ 2), 0, 1 + ω ^ 2, 1, 0, 1]

/-- The coordinate (in `Fin 8`) of the edge represented by each row of `rim`. -/
def coord : Fin 6 → Fin 8 := ![0, 1, 2, 4, 5, 6]

/-- The first vertex of the edge represented by each row of `rim`. -/
def edgeFst : Fin 6 → Fin 3 := ![0, 0, 1, 0, 0, 1]

/-- The second vertex of the edge represented by each row of `rim`. -/
def edgeSnd : Fin 6 → Fin 3 := ![1, 2, 2, 1, 2, 2]

/-- The rows of `rim` exhaust exactly the nonempty edges of `badHypergraph`. -/
theorem badHypergraph_coord_eq : ∀ r : Fin 6,
    badHypergraph (coord r) = {edgeFst r, edgeSnd r} := by decide

theorem edgeFst_mem : ∀ r : Fin 6, edgeFst r ∈ badHypergraph (coord r) := by decide

theorem edgeSnd_mem : ∀ r : Fin 6, edgeSnd r ∈ badHypergraph (coord r) := by decide

/-- The k-wpc weight of `badHypergraph` is *tight*: under the discrete (identity) labeling
the weight is `Σᵢ (|Eᵢ| - 1) = 6 = k(s - 1)` with `k = 3`, `s = 3` — even minimal
3-wpc hypergraphs fail the derandomization property. -/
theorem badHypergraph_weight_tight : labelWeight badHypergraph id = 6 := by decide

/-- The first block of `rimKernelVec` is the coefficient vector of the certificate
polynomial `p₀`. -/
theorem rimKernelVec_poly₀ :
    C (rimKernelVec ω 0) + C (rimKernelVec ω 1) * X + C (rimKernelVec ω 2) * X ^ 2 =
      p₀ ω := by
  simp only [rimKernelVec, p₀, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    map_mul, map_add, map_neg, map_one, map_pow, map_zero]
  ring

/-- The second block of `rimKernelVec` is the coefficient vector of the certificate
polynomial `p₁`. -/
theorem rimKernelVec_poly₁ :
    C (rimKernelVec ω 3) + C (rimKernelVec ω 4) * X + C (rimKernelVec ω 5) * X ^ 2 =
      (p₁ : F[X]) := by
  simp only [rimKernelVec, p₁]
  norm_num
  ring

/-- **Kernel ↔ certificate bridge.**  Row `r` of `rim ω` dotted with `rimKernelVec ω`
computes exactly the difference of certificate evaluations across the edge represented by
that row, at the geometric point `ω^(coord r)`.  This is an identity in `ω` (no hypothesis
on `ω` is needed): it states that `rim` *is* the reduced intersection matrix of
`badHypergraph` and `rimKernelVec` *is* the coefficient encoding of the certificate. -/
theorem rim_mulVec_eq_certDiff (r : Fin 6) :
    (rim ω *ᵥ rimKernelVec ω) r =
      ((cert ω) (edgeFst r)).eval (ω ^ ((coord r : Fin 8) : ℕ)) -
        ((cert ω) (edgeSnd r)).eval (ω ^ ((coord r : Fin 8) : ℕ)) := by
  fin_cases r <;>
    simp [rim, rimKernelVec, cert, p₀, p₁, coord, edgeFst, edgeSnd,
      Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;>
    ring

/-- The certificate vector lies in the kernel of the RIM at the geometric point: with
`ω⁴ = -1`, every row evaluates to an agreement difference that vanishes. -/
theorem rim_mulVec_rimKernelVec (hω : ω ^ 4 = -1) : rim ω *ᵥ rimKernelVec ω = 0 := by
  funext r
  rw [rim_mulVec_eq_certDiff ω r, Pi.zero_apply, sub_eq_zero]
  exact certificate_eval_agree ω hω (coord r) (edgeFst r) (edgeFst_mem r) (edgeSnd r)
    (edgeSnd_mem r)

/-- The kernel certificate vector is nonzero (its fourth entry, the constant coefficient
of `p₁`, is `1`). -/
theorem rimKernelVec_ne_zero : rimKernelVec ω ≠ 0 := by
  intro h
  have h3 := congr_fun h 3
  simp [rimKernelVec] at h3

/-- **Determinant drop.**  The RIM of the ±-pair hypergraph at the geometric point is
singular whenever `ω⁴ = -1`.  (Symbolically: `Φ₈(q)` divides `D(q)`.) -/
theorem rim_det_eq_zero (hω : ω ^ 4 = -1) : (rim ω).det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨rimKernelVec ω, rimKernelVec_ne_zero ω, rim_mulVec_rimKernelVec ω hω⟩

/-- **Column-rank drop.**  The RIM of the ±-pair hypergraph at the geometric point has
column rank `< 6` whenever `ω⁴ = -1` — full column rank is precisely the property consumed
by the AGL24/GZ capacity machinery. -/
theorem rim_rank_lt_six (hω : ω ^ 4 = -1) : (rim ω).rank < 6 := by
  have hker : rimKernelVec ω ∈ LinearMap.ker (rim ω).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact rim_mulVec_rimKernelVec ω hω
  have hpos : 0 < Module.finrank F (LinearMap.ker (rim ω).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨rimKernelVec ω, hker⟩, by
        simpa [Submodule.mk_eq_zero] using rimKernelVec_ne_zero ω⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker (rim ω).mulVecLin
  rw [Module.finrank_fin_fun] at hsum
  have hrank : (rim ω).rank = Module.finrank F (LinearMap.range (rim ω).mulVecLin) := rfl
  rw [hrank]
  omega

/-- **The packaged matrix-level refutation**: there is a 3-weakly-partition-connected
agreement hypergraph on the 8 geometric coordinates `ω⁰, …, ω⁷` whose reduced intersection
matrix at the geometric point is singular and column-rank-deficient.  The universal
μ_{2^t} RIM full-rank derandomization target is therefore false over every field with an
element `ω` satisfying `ω⁴ = -1` (e.g. any `ω` of order 8). -/
theorem rim_rank_drop (hω : ω ^ 4 = -1) :
    IsWeaklyPartitionConnected badHypergraph 3 ∧ (rim ω).det = 0 ∧ (rim ω).rank < 6 :=
  ⟨badHypergraph_kwpc, rim_det_eq_zero ω hω, rim_rank_lt_six ω hω⟩

/-! ## Concrete first certificate over `F₁₇`

`ω = 9` has order 8 in `ZMod 17` (`9⁴ = 6561 ≡ -1`), matching the mod-`p` run of
`pmpair_counterexample.py`: rank 5 < 6 with kernel certificate `(5, 0, 14, 1, 0, 1)`. -/

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem nine_pow_four_zmod17 : (9 : ZMod 17) ^ 4 = -1 := by decide

/-- The fully numeric RIM over `F₁₇` at `ω = 9`. -/
theorem rim_zmod17_eq :
    rim (9 : ZMod 17) =
      !![1, 1, 1, 16, 16, 16;
         1, 9, 13, 0, 0, 0;
         0, 0, 0, 1, 13, 16;
         1, 16, 1, 16, 1, 16;
         1, 8, 13, 0, 0, 0;
         0, 0, 0, 1, 4, 16] := by
  decide

/-- The fully numeric kernel certificate over `F₁₇`, as found by the mod-`p` search. -/
theorem rimKernelVec_zmod17_eq :
    rimKernelVec (9 : ZMod 17) = ![5, 0, 14, 1, 0, 1] := by
  decide

theorem rim_det_eq_zero_zmod17 : (rim (9 : ZMod 17)).det = 0 :=
  rim_det_eq_zero _ nine_pow_four_zmod17

theorem rim_rank_lt_six_zmod17 : (rim (9 : ZMod 17)).rank < 6 :=
  rim_rank_lt_six _ nine_pow_four_zmod17

end MuTwoPowDerandRefutation
