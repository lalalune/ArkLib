# NOVEL probe: cube-Fourier (hypercube harmonic analysis) of the dyadic Gauss period — refutes FKN lever, reduces to EVT, 2026-06-15

## The novel reframing (a genuinely fresh domain, not in the dead ledger)
Write the discrete-log exponent j ∈ Z/2^μ in binary, j = Σ x_i 2^i. Then for ζ = primitive 2^μ-th
root and ω_i = ζ^{2^i}, the dyadic Gauss period becomes a function on the BOOLEAN CUBE {0,1}^μ:
  η_b = Σ_{x ∈ {0,1}^μ} e_p(b · m(x)),   m(x) = Π_i ω_i^{x_i}   (multiplicative monomial in the ω_i).
So f(x) = e_p(b·m(x)) is a unit-modulus function on the hypercube; its cube-Walsh transform
hat f(S) = (1/n)Σ_x f(x)(-1)^{S·x} has hat f(0) = η_b/n. Parseval: Σ_S |hat f(S)|² = 1. The prize
M(n) ≤ C√(n log m) ⟺ the worst-b DC coefficient |hat f(0)| ≤ C√(log m / n). This is harmonic analysis
on {0,1}^μ via the binary digits of the discrete log — a domain NOT in the #444 §8 dead ledger.

## What the probes found (exact worst-b, n = 8,16,32,64 at β=4, p ≈ n⁴)
- **Spectrum is NOT flat** (first refutation survived): top mode / flat = 7.1, 12.0, 16.5, ... (grows);
  the top μ = log₂n modes carry 0.99, 0.84, 0.74, ... of the energy (heavy head).
- **BUT it is NOT low-Walsh-degree** (the FKN/junta lever, the hoped-for new structure): energy by
  Hamming weight of S spreads toward the MIDDLE as n grows —
  DC fraction (weight 0): 0.893 → 0.748 → 0.516 → 0.362;  weight≤2 fraction: 0.992 → 0.910 → 0.691 →
  0.559; at n=64 weight-3 alone carries 0.323. The Walsh degree GROWS with n; no bounded-degree/junta
  structure. **FKN / low-degree lever REFUTED.**
- **Effective support is Θ(n)** (participation ratio PR/n ≈ 0.11 ≈ const): NOT sparse enough for a
  sparse-recovery / Goldreich-Levin lever. Heavy-headed but full-support.

## Why it reduces to the wall (via EVT, honest)
"Energy spreading to middle Walsh weights" ⟺ f(x) = e_p(b·m(x)) behaves like a RANDOM unit-modulus
function on the cube. A random such f has |hat f(0)| ~ Gaussian(0, 1/n), so a single η_b ~ √n; the
WORST b = the max of ~p (≈ q) such DC coefficients ~ √(log q)/√n, giving M ~ √(n log q) — EXACTLY the
conjectured form. So the cube-Fourier reframing makes the prize the statement "the {η_b} behave like the
max of q independent Gaussian cube-DCs" = the i.i.d.-Gaussian EXTREME-VALUE-THEORY heuristic. That crown
(FHK/GMC/BRW/Gaussian-EVT) is already in the #444 §8 dead ledger (killed as a *proof* route by the
two-value normalizer spike; it remains the HEURISTIC justification of the conjecture, not a proof).

## Honest verdict
A genuinely novel reframing (cube harmonic analysis of the dyadic Gauss period) that:
- ELIMINATES the FKN/low-degree/junta and sparse-recovery levers (the spectrum is high-degree,
  full-support) — a new route-elimination for the §8 dead ledger.
- REDUCES the prize to the i.i.d.-Gaussian EVT heuristic (the conjecture's own heuristic = the open
  wall). NOT a new lever, NOT a closure.
This is the honest result of one "bold conjecture → refute" iteration on the core. The prize stays the
BGK/Paley √-cancellation wall; the cube view confirms WHY (the η_b are random-like, so the worst-b is an
EVT max — and proving Gaussian-like tails for thin-subgroup Gauss periods IS the open problem).
Probes: /tmp/cube_spectrum.py, /tmp/cube_weight.py.
