# CORRECTION: the DFT-uncertainty result pins the COVERING radius (n/2+Θ(k)), NOT δ* — δ* is the LIST object (#444)

The uncertainty-bound army (14 angles, rigorous, verified to n=1024) settled the DFT max-zeros object EXACTLY —
but multiple agents independently flagged that it is a DIFFERENT object from the prize δ*. Honest correction to
the earlier "smooth-domain hardness = DFT uncertainty principle" framing (commits 63aa3b4ab, 6507e61aa).

## The rigorous result (covering / max-zeros object — SOLVED)

For n=2^μ, the max number of zeros in μ_n of a (k+2)-term lacunary polynomial with support {0..k−1,a,b}
(= n − min-support of a Fourier-sparse function = the DFT uncertainty quantity) is EXACTLY:

> **s*_cover(n,k) = n/2 + 2^⌊log₂(k−1)⌋**   (verified n=8..4096, k=2..32; engine + 2 independent re-derivations)

- **δ*_cover = 1 − s*_cover/n → 1/2** (a PLOTKIN-regime THIRD answer — NEITHER Johnson √(kn) NOR floor k+Θ(n/log n)).
- **Explicit construction:** `P(t) = (t^{n/2}−1)(t^m + γ)`, `m = 2^⌊log₂(k−1)⌋ ≤ k−1`, `γ = −ζ_n^m`. Support
  `{0, m, n/2, n/2+m}` is a valid far line. Zeros = all of μ_{n/2} (n/2 points, from `t^{n/2}=1`) + the m m-th
  roots of −γ (land at odd indices, disjoint from the even subgroup). Total n/2 + m.
- **Mechanism (one-line proof):** on μ_{n/2}, `z^{n/2}=1` collapses the support {0..k−1,a,b} mod n/2 to ≤k
  exponents; a k-equation system on k+2 coefficients leaves a ≥2-dim space vanishing on the whole index-2
  subgroup; 1 free parameter kills m extra antipodal points. The order-2 character `z^{n/2}` is the unique
  **2-torsion** of Z_{2^μ} — ABSENT for prime n (Tao ⟹ s*=k+2 ⟹ capacity). So the 2-torsion is exactly what
  makes the covering radius large for the smooth domain.

## THE CRITICAL CORRECTION: covering ≠ δ*

The DFT uncertainty / max-zeros (Object A) is NOT the prize δ* (Object B):
- **Object A (covering / max-zeros / min-support):** = n/2 + 2^⌊log₂(k−1)⌋. The max agreement of ONE worst word
  with a codeword. SOLVED (this result). δ → 1/2 (Plotkin).
- **Object B (the prize δ* = LIST-decoding binding):** the smallest s where the COUNT `#{γ : x^a+γx^b agrees on
  ≥ s points} ≤ budget = n`. This is a γ-COUNT / list-size threshold, NOT the single-word max. At n=16,k=4:
  Object A = 10 but Object B = 7. **DIFFERENT objects.**
- The in-tree `scripts/rust-pg/src/bin/unclist.rs` already names this split: "(1) COVERING max-zeros = pure DFT
  uncertainty vs (2) LIST = prize-relevant."

So my earlier "δ* = DFT uncertainty principle on Z_{2^μ}" was IMPRECISE: the uncertainty principle pins the
COVERING radius (now solved, = n/2+Θ(k), Plotkin), but the prize δ* is the **LIST-decoding (γ-count) object**,
which remains the open BGK/sup-norm wall. The covering result does NOT touch δ*.

## What this leaves for the prize

The prize δ* = the LIST-decoding binding (Object B) = explicit-smooth-RS list size past Johnson = the open core
(BChKS equivalence, Hab25 Lemma 1 floor mechanism). The covering radius is a clean solved side-result; the
list/γ-count object is where Johnson-vs-floor (and the whole BGK reduction) actually lives. Measured: the list
binding s*_list ~ Θ(√(kn)) (Johnson-ish, ratio 0.75–0.90) at feasible n — but Johnson and floor coincide there,
so undecided asymptotically (the c.348 retraction stands).

NET: a clean rigorous covering-radius theorem (new math) + an honest correction (it is not δ*). The prize remains
the list-decoding object. The 2-torsion mechanism (why smooth n is special vs prime n) is genuinely insightful
and may transfer to the list object — worth pursuing.
