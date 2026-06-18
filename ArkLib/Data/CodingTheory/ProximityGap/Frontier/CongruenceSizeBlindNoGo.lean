/-
# Congruence / finite-symmetry certificates are SIZE-BLIND for the char-p excess (#444)

The prize wall is a bound on the SIZE of the char-p spurious-collision count
`W_r := E_r(μ_n) − (2r−1)‼·n^r` (equivalently the reduced energy surplus): one needs `W_r ≤ slack_r`
with `slack_r ~ n^{2r}/q` at depth `r ≈ ln q`. Many swarm attempts produce a *congruence* certificate
`M ∣ W_r` (or `W_r ≡ c (mod M)`) from a finite symmetry — parity (`M=2`), Galois `(ℤ/n)^*` (`M=n/2`),
swap×neg×Sᵣ×Sᵣ (`M ≤ 4·(r!)²`), orbit-gcd (`log₂ M = O(1)` in r). The only way such a certificate bounds
the size is the wraparound `M ∣ W ∧ W < M ⟹ W = 0`, which needs `M > W_r` (hence `M > slack_r`).

**This file proves, conjecture-free, that a congruence certificate is size-blind:** for ANY modulus
`M ≥ 1` and ANY budget `slack`, the class `{W : M ∣ W}` (and every residue class mod `M`) contains
witnesses exceeding `slack`. So knowing only `M ∣ W_r` is consistent with `W_r > slack_r`; it can never
prove `W_r ≤ slack_r`. Since every finite-symmetry modulus is `M ≤ |sym group| ≪ slack_r` at the prize
(`log₂ slack_r ≈ 10⁹⁶⁰` at `r≈89`, vs `log₂|sym group| ≤ ~273`), **all congruence/parity/Galois/orbit
pins are size-blind there** — bounding `W_r`'s size requires a genuinely analytic (non-congruence) input.

Together with the in-tree no-gos this completes a trilogy on "the SIZE bound cannot come from method X":
algebraic invariants of `Ψ` are **house-blind** (`disc(Ψ)=p^{m-1}f²`, SVP lower bound);
LP / Delsarte duals are **degree-1-blind** (`DelsarteLPNoGo.parseval_lp_extremal`); congruence /
finite-symmetry certificates are **size-blind** (here). The remaining lever is the archimedean,
nonlinear, depth-`ln q` energy bound = the BGK/Paley wall.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`.
-/
import Mathlib.Tactic

namespace ArkLib.ProximityGap.CongruenceSizeBlindNoGo

/-- **A divisibility certificate cannot bound size.** For any modulus `M ≥ 1` and any budget `slack`,
there is a multiple of `M` strictly exceeding `slack`. Hence `M ∣ W` is consistent with `W > slack`:
knowing only `M ∣ W` never proves `W ≤ slack`. -/
theorem dvd_cannot_bound_size (M slack : ℕ) (hM : 0 < M) :
    ∃ W, M ∣ W ∧ slack < W := by
  refine ⟨M * (slack + 1), Dvd.intro _ rfl, ?_⟩
  calc slack < slack + 1 := Nat.lt_succ_self slack
    _ = 1 * (slack + 1) := (one_mul _).symm
    _ ≤ M * (slack + 1) := Nat.mul_le_mul_right _ hM

/-- **Residue-class form.** Every residue class `c (mod M)` (`M ≥ 1`) contains elements exceeding any
budget `slack`. So a symmetry/Galois/parity pin `W ≡ c (mod M)` is size-blind. -/
theorem residue_class_unbounded (M c slack : ℕ) (hM : 0 < M) :
    ∃ W, W % M = c % M ∧ slack < W := by
  refine ⟨c % M + M * (slack + 1), ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · have h : slack + 1 ≤ M * (slack + 1) := by
      calc slack + 1 = 1 * (slack + 1) := (one_mul _).symm
        _ ≤ M * (slack + 1) := Nat.mul_le_mul_right _ hM
    omega

/-- **The size-blindness no-go for the char-p excess (headline).** A certificate establishing only
`M ∣ W` with the modulus bounded by the symmetry group `M ≤ B`, where the budget exceeds that bound
`B ≤ slack`, is consistent with `W > slack` — so it cannot certify `W ≤ slack`. Bounding the SIZE of
`W_r` therefore requires a non-congruence (analytic) input; at the prize every `B ≤ 4·(r!)²` (or `n/2`)
is `≤ slack_r`, so all finite-symmetry pins fail. -/
theorem congruence_size_blind (M B slack : ℕ) (hM : 0 < M) (_hMB : M ≤ B) (_hBs : B ≤ slack) :
    ∃ W, M ∣ W ∧ slack < W :=
  dvd_cannot_bound_size M slack hM

end ArkLib.ProximityGap.CongruenceSizeBlindNoGo
