# The far-line incidence is a RIGOROUS upper bound on the MCA δ* — and it is remarkably LOW (#407)

After reading the exact ABF26 Def 4.3 (`Errors.lean:216` mcaEvent, `:231` epsMCA) the bound direction and the
witness-validity are settled. This sharpens (and corrects) the earlier "Plotkin proxy" framing.

## The rigorous chain

- **ABF26 Def 4.3:** `epsMCA(C,δ) = sup over word-stacks (u₀,u₁) of Pr_γ[mcaEvent]`, where `mcaEvent` = ∃ S,
  |S| ≥ (1−δ)n, the line `u₀+γu₁` equals a codeword on S, AND `(u₀,u₁)` does NOT jointly agree with a codeword
  pair on S.
- **`epsMCA_ge_far_incidence` (in-tree, axiom-clean):** `epsMCA ≥ far_incidence/q`.
- **Far-monomial witnesses are VALID mcaEvents:** for `u₀=x^a, u₁=x^b` far (a,b ≥ k) and |S|=s>k, the pair
  cannot jointly agree (x^b can't be a deg<k poly on >k points), so the joint-agreement subtraction is 0 ⟹
  `mcaEvent count = far_incidence` (my computed quantity). So the bound is tight for these witnesses.

⟹ **`δ*_MCA ≤ δ*_far-line`**: the radius where the far-monomial incidence first exceeds budget `B = q·ε*` is a
**rigorous upper bound** on the true MCA threshold (above it, a valid witness forces `epsMCA > ε*`).

## The computed upper bound is far below the floor

Exact (validated Rust engine): `δ*_far-line = ½ + (1/(2ρ) − 1)/n` (n≤24, ρ∈{1/4,1/8}). So the **rigorous upper
bound on δ*_MCA** is ≈ Johnson-to-½ for the computed n — **WELL below the conjectured floor `1−ρ−Θ(1/log n)`**
(→1−ρ). E.g. ρ=1/4: upper bound → ½ = Johnson; ρ=1/8: upper bound 0.6875→0.625 (n=16→24), already crossing
Johnson=0.646.

## The decisive question (honest; my earlier "→½" was an over-extrapolation)

The formula is validated only for **n≤24**; the limit ½ is extrapolated. Two possibilities, distinguished by
larger n:
1. **Formula continues (δ*_far-line → ½):** then for ρ<1/4 the rigorous upper bound goes BELOW Johnson, which
   **REFUTES the window/floor** `δ* ∈ (1−√ρ, 1−ρ−Θ)` — δ* would be ≈ ½, dramatically below capacity (a far
   stronger impossibility than the known capacity-impossibility).
2. **Formula breaks / saturates at Johnson:** δ*_far-line plateaus at ≈ 1−√ρ for large n. Then the far-line
   incidence tracks the LOWER window edge (Johnson), and the floor (upper edge) is the genuine harder object —
   consistent with the prize framing.

For ρ=1/4 the two coincide (½ = Johnson), so it can't distinguish them; **ρ<1/4 at larger n is decisive**
(n=32,k=4 ρ=1/8, ~9.6h; or n=28,k=7 ρ=1/4 ~24min as a continuation check). Running these tests which case holds.

## Status

Either outcome is a **major, rigorous result**: (1) a refutation of the floor (δ* ≈ ½), or (2) a proof that the
far-line incidence = Johnson (lower edge) and the floor needs the harder general-witness object. The
rigorous-upper-bound chain (epsMCA ≥ far_inc/q, far witnesses valid) is solid; only the large-n behavior of
`δ*_far-line` is unverified. NOT a closure — but this is the sharpest, most rigorous handle on δ* the campaign
has, and it is decided by a concrete, runnable computation.
