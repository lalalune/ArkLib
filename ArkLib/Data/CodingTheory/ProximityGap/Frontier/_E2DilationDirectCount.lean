/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy

/-!
# Attack 2: the DIRECT (Cauchy–Schwarz-free) count of the `e₂ = 0` bad-scalar locus (#407)

ABF26 Thm 5.1 / the W2 second-moment bound carry a square root: `ε_mca` is bounded by
`L²·δn` via a Cauchy–Schwarz `L² → L^∞` step (`T² ≤ |G|·E`). For Reed–Solomon the bad-scalar set
of the two-monomial pencil `x^k + α x^{k+2}` at agreement `k+2` is NOT a random `L²` object: it is
the **rigid algebraic locus** `{S : e₂(S) = 0, e₁(S) ≠ 0}`, with the bad scalar pinned to
`α(S) = −1/e₁(S)` (`E2VanishEnergy.badScalar_of_energy`). Attack 2 asks: does this rigidity give a
*direct* count of bad scalars — linear, with **no Cauchy–Schwarz `√`** — and if so, what is the
residual?

This file lands the **exact algebraic structure of the direct count**: the `e₂ = 0` locus, and its
image under the bad-scalar map `S ↦ −1/e₁(S)`, are **closed under scalar dilation** `S ↦ u • S`
(`u ≠ 0`). Concretely:

* `e1_smul` / `p2_smul` — `e₁(u • S) = u · e₁(S)`, `p₂(u • S) = u² · p₂(S)` (the power sums scale
  homogeneously);
* `e2_smul` — `e₂(u • S) = u² · e₂(S)` (the second elementary symmetric is degree-2 homogeneous);
* `e2_zero_smul` — the locus `e₂ = 0` is **scale-invariant**: `e₂(S) = 0 ⟹ e₂(u • S) = 0`;
* `badScalar_smul` — the bad scalar transforms **multiplicatively**: `α(u • S) = u⁻¹ · α(S)`, i.e.
  the bad-scalar set is **closed under multiplication by `u⁻¹`** for every `u ≠ 0`.

Specialised to dilation by the subgroup `μ_n` (the prize domain; each `u ∈ μ_n` permutes `μ_n`,
mapping `(k+2)`-subsets to `(k+2)`-subsets), this says the bad-scalar set is a **union of full
`μ_n`-cosets**, hence

  > **`#{bad α} = n · K`,  `K := #{dilation-orbits of e₁(S) over the e₂ = 0 locus}`.**

`badScalarSet_card_eq_orbit_mul` formalises the count form (over a finite scalar group `G` acting
freely on the bad-scalar set: `#bad = |G| · #orbits`).

## The honest verdict (the precise obstruction)

The direct count **does remove both square roots** of the W2/ABF chain — it is an *exact* algebraic
cardinality `n · K`, with no `T² ≤ |G|·E` Cauchy–Schwarz step and no Johnson-transform radius `√`.
But the count does **not** collapse to `O(n)`: the residual `K(n)` (the orbit census of the
extremal `e₂ = 0` locus) is **super-linear**, measured (probe `probe_e2_n32.py`, prize-regime prime
`p = n⁴`, extremal width `w = n/2`):

| `n`  | `K` (orbit count) | `#{bad α} = n·K` |
|------|-------------------|------------------|
| 8    | 1                 | 8                |
| 16   | 3                 | 48               |
| 32   | 38                | 1216             |

So Attack 2 **re-collapses to the `e₂ = 0` extremal orbit count `K(n)`**, which is open — it is the
additive-energy / negation-pair excess (the SAME object `E_r(μ_n)` that the BGK route bounds), now
exposed as an *exact combinatorial census* rather than an `L²` energy. The rigidity converts the
analytic `√` (Cauchy–Schwarz) into a **computable-but-large** count; it does NOT make the count
small. This file pins the *exact reduction* `direct count = n · K` and the dilation rigidity that
makes it well-defined; the residual is `K`, the open extremal census (not BGK directly, but its
combinatorial twin).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.E2VanishEnergy

namespace ArkLib.ProximityGap.E2DilationDirectCount

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Dilation of a finite node set.** `u • S := S.image (u * ·)`, the image of `S` under
multiplication by `u`. For `u ≠ 0` this is an injective relabelling, so `#(u • S) = #S`. -/
noncomputable def dil (u : F) (S : Finset F) : Finset F := S.image (fun s => u * s)

/-- For `u ≠ 0`, dilation preserves the cardinality: `#(u • S) = #S` (multiplication by a unit is
injective). -/
theorem dil_card {u : F} (hu : u ≠ 0) (S : Finset F) : (dil u S).card = S.card := by
  unfold dil
  rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu)]

/-- For `u ≠ 0`, membership in the dilate: `x ∈ u • S ↔ u⁻¹ x ∈ S`. -/
theorem mem_dil {u : F} (hu : u ≠ 0) (S : Finset F) (x : F) :
    x ∈ dil u S ↔ u⁻¹ * x ∈ S := by
  unfold dil
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  · intro h
    exact ⟨u⁻¹ * x, h, by rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]⟩

/-- **`e₁` scales linearly:** `e₁(u • S) = u · e₁(S)`. The first power sum is degree-1 homogeneous.
Needs `u ≠ 0` so that `(u * ·)` is injective on `S` (`Finset.sum_image`). -/
theorem e1_smul {u : F} (hu : u ≠ 0) (S : Finset F) : e1 (dil u S) = u * e1 S := by
  classical
  unfold e1 dil
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hu h), Finset.mul_sum]

/-- **`p₂` scales quadratically:** `p₂(u • S) = u² · p₂(S)`. The second power sum is degree-2
homogeneous. -/
theorem p2_smul {u : F} (hu : u ≠ 0) (S : Finset F) : p2 (dil u S) = u ^ 2 * p2 S := by
  classical
  unfold p2 dil
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hu h), Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **`e₂` scales quadratically:** `e₂(u • S) = u² · e₂(S)`. The second elementary symmetric is
degree-2 homogeneous, via `e₂ = (e₁² − p₂)/2` and the scalings of `e₁`, `p₂`. -/
theorem e2_smul {u : F} (hu : u ≠ 0) (S : Finset F) : e2 (dil u S) = u ^ 2 * e2 S := by
  rw [e2_eq, e2_eq, e1_smul hu, p2_smul hu]
  ring

/-- **The `e₂ = 0` locus is scale-invariant.** If `e₂(S) = 0` then `e₂(u • S) = 0` for every
`u ≠ 0`: dilation preserves the vanishing of the second elementary symmetric. This is the algebraic
fact that makes the bad-scalar set a *union of `μ_n`-cosets*. -/
theorem e2_zero_smul {u : F} (hu : u ≠ 0) {S : Finset F} (hS : e2 S = 0) : e2 (dil u S) = 0 := by
  rw [e2_smul hu, hS, mul_zero]

/-- **`e₁ ≠ 0` is scale-invariant** (for `u ≠ 0`): the nonvanishing of the first power sum
(the eligibility of the bad scalar `α = −1/e₁`) is preserved by dilation. -/
theorem e1_ne_zero_smul {u : F} (hu : u ≠ 0) {S : Finset F} (hS : e1 S ≠ 0) :
    e1 (dil u S) ≠ 0 := by
  rw [e1_smul hu]
  exact mul_ne_zero hu hS

/-- **The bad scalar transforms multiplicatively:** `α(u • S) = u⁻¹ · α(S)`, where
`α(S) := −1/e₁(S)` is the bad scalar of the two-monomial pencil at the `e₂ = 0` locus
(`E2VanishEnergy.badScalar_of_energy`). Hence the bad-scalar SET is **closed under multiplication
by `u⁻¹`** for every `u ≠ 0`: dilating the node set by `u` dilates the bad scalar by `u⁻¹`. -/
theorem badScalar_smul {u : F} (hu : u ≠ 0) (S : Finset F) :
    -(e1 (dil u S))⁻¹ = u⁻¹ * (-(e1 S)⁻¹) := by
  rw [e1_smul hu, mul_inv, mul_comm u⁻¹ _]
  ring

/-! ## The count form: `#{bad α} = n · K`

A finite multiplicative subgroup of `F` (as a `Finset F`) — concretely `μ_n` — acts on the
bad-scalar set by multiplication. The orbit of any nonzero `x` has *exactly* `n` elements (the
action is free since `x ≠ 0`), and orbits partition the set, giving the exact count
`#{bad α} = n · #{orbits}`. We package the subgroup as a `Finset F` with explicit group axioms
(self-contained; instantiate at `μ_n = rootsOfUnity n`). -/

/-- A finite multiplicative subgroup of `F`, recorded as a `Finset F` with the group axioms.
`one_mem`, `mul_mem`, `inv_mem` (closure under the field inverse), and `zero_notMem` (every element
is a unit). The intended instance is `μ_n` (the `n`-th roots of unity). -/
structure FinSubgroup (G : Finset F) : Prop where
  one_mem : (1 : F) ∈ G
  mul_mem : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G
  inv_mem : ∀ a ∈ G, a⁻¹ ∈ G
  zero_notMem : (0 : F) ∉ G

/-- **The orbit of `x` under the dilation action of `G`:** `G • x = {u·x : u ∈ G}`. -/
noncomputable def orbit (G : Finset F) (x : F) : Finset F := G.image (fun u => u * x)

/-- **Each orbit has exactly `#G` elements** (free action). For `x ≠ 0`, `u ↦ u·x` is injective on
`G`, so the orbit `G • x` has cardinality `#G`. This is the precise "every bad-`α` value spawns a
full `μ_n`-coset of bad values" structural fact: the orbit is a complete coset of size `n`. -/
theorem orbit_card {G : Finset F} {x : F} (hx : x ≠ 0) : (orbit G x).card = G.card := by
  unfold orbit
  exact Finset.card_image_of_injective _ (mul_left_injective₀ hx)

/-- `x` itself lies in its orbit (`1 ∈ G`). -/
theorem self_mem_orbit {G : Finset F} (hG : FinSubgroup G) (x : F) : x ∈ orbit G x := by
  unfold orbit
  rw [Finset.mem_image]
  exact ⟨1, hG.one_mem, one_mul x⟩

/-- **Orbits are `G`-stable**: if `g ∈ G` then `g · y ∈ orbit G x` whenever `y ∈ orbit G x`. -/
theorem smul_mem_orbit {G : Finset F} (hG : FinSubgroup G) {g x y : F} (hg : g ∈ G)
    (hy : y ∈ orbit G x) : g * y ∈ orbit G x := by
  unfold orbit at hy ⊢
  rw [Finset.mem_image] at hy ⊢
  obtain ⟨u, hu, rfl⟩ := hy
  exact ⟨g * u, hG.mul_mem _ hg _ hu, by ring⟩

/-- **Orbits coincide or are disjoint — equality form.** If `y ∈ orbit G x` then
`orbit G y = orbit G x`. (Standard group-action orbit lemma; uses closure and inverses.) -/
theorem orbit_eq_of_mem {G : Finset F} (hG : FinSubgroup G) {x y : F} (hy : y ∈ orbit G x) :
    orbit G y = orbit G x := by
  unfold orbit at hy ⊢
  rw [Finset.mem_image] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v * u, hG.mul_mem _ hv _ hu, by ring⟩
  · rintro ⟨v, hv, rfl⟩
    -- z = v * x ; write x = u⁻¹ * (u * x), so z = (v * u⁻¹) * (u * x)
    refine ⟨v * u⁻¹, hG.mul_mem _ hv _ (hG.inv_mem _ hu), ?_⟩
    have hune : u ≠ 0 := fun h => hG.zero_notMem (h ▸ hu)
    field_simp

/-- **The exact direct count: `#B = #G · K`.** Let `B` be a `Finset F` of *nonzero* scalars that is
**closed under dilation by `G`** (the bad-scalar set: closed under `μ_n` by `badScalar_smul`, and
`0 ∉ B` since `α = −1/e₁ ≠ 0`). Then `B` partitions into `G`-orbits, each of size exactly `#G`, so

  `#B = #(orbit representatives) · #G  =  #G · K`.

Here `K := #(B.image (orbit G ·))` is the number of distinct orbits. Specialised to `G = μ_n`
(`#G = n`), this is the exact reduction **`#{bad α} = n · K`** — the Cauchy–Schwarz-free direct
count. The residual `K` is the open extremal orbit census (super-linear in `n`; see the file
header), NOT a closed `O(n)` bound. -/
theorem badScalarSet_card_eq_orbit_mul {G : Finset F} (hG : FinSubgroup G) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    B.card = (B.image (fun x => orbit G x)).card * G.card := by
  classical
  -- partition B by orbit, each fiber is the orbit (size #G)
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x => orbit G x) (t := B.image (fun x => orbit G x))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
  -- each fiber {x ∈ B | orbit G x = O} equals the orbit O, hence has card #G
  rw [Finset.sum_congr rfl (g := fun _ => G.card) ?_, Finset.sum_const, smul_eq_mul]
  intro O hO
  rw [Finset.mem_image] at hO
  obtain ⟨x₀, hx₀B, rfl⟩ := hO
  have hx₀ne : x₀ ≠ 0 := fun h => hB0 (h ▸ hx₀B)
  -- the fiber over `orbit G x₀` is exactly `orbit G x₀`
  have hfiber : (B.filter (fun x => orbit G x = orbit G x₀)) = orbit G x₀ := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hz⟩
      rw [← hz]; exact self_mem_orbit hG z
    · intro hz
      have hzB : z ∈ B := by
        -- z = u * x₀ for some u ∈ G, and B is G-stable
        unfold orbit at hz
        rw [Finset.mem_image] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        exact hBstable u hu x₀ hx₀B
      exact ⟨hzB, orbit_eq_of_mem hG hz⟩
  rw [hfiber, orbit_card hx₀ne]

/-- **`#G ∣ #B`** — the divisibility corollary: the size of the bad-scalar set is divisible by the
order of the dilation subgroup. For `G = μ_n` this is `n ∣ #{bad α}`, the clean statement that the
direct count is a multiple of `n` (a union of full `n`-cosets). -/
theorem badScalarSet_card_dvd {G : Finset F} (hG : FinSubgroup G) {B : Finset F}
    (hB0 : (0 : F) ∉ B) (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    G.card ∣ B.card := by
  rw [badScalarSet_card_eq_orbit_mul hG hB0 hBstable]
  exact Dvd.intro_left _ rfl

end ArkLib.ProximityGap.E2DilationDirectCount

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.dil_card
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.mem_dil
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.e1_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.p2_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.e2_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.e2_zero_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.e1_ne_zero_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.badScalar_smul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.orbit_card
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.self_mem_orbit
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.smul_mem_orbit
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.orbit_eq_of_mem
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.badScalarSet_card_eq_orbit_mul
#print axioms ArkLib.ProximityGap.E2DilationDirectCount.badScalarSet_card_dvd
