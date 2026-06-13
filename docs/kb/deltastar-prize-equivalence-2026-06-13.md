# The prize is (R) ⟺ explicit-RS beyond-Johnson list-decoding — research synthesis 2026-06-13

Decisive literature + computational synthesis of where the proximity prize (δ* for smooth-domain
RS) actually stands, after the governing-law reduction to the far-line incidence (R).

## THE EQUIVALENCE (the prize is a recognized major open problem)

**Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, "On Proximity Gaps for Reed-Solomon Codes"
(ePrint 2025/169), Theorem 1.9.** For `C = RS[F_q, D, k]`, `k=(1−δ)n`, with `τ = LDR(δ)+2/n`
(just past the list-`q` decoding radius): there exist `f,g:D→F_q` with
`|{z : Δ(f+zg, C) ≤ τ}| ≥ q/(2n)` yet `Δ([f,g], C²) ≥ 1−1/n`. **Consequence: improving the
proximity-gap (= line–ball incidence = our (R)) radius beyond Johnson for ANY RS code IMPLIES
list-decoding that code beyond Johnson with list ≤ q.** The two are equivalent.

- They **DISPROVE** the `n^γ`-bounded proximity-gaps conjecture for all `γ=O(1)`, and (with
  ePrint 2025/2046, Crites–Stewart) the **correlated-agreement-up-to-capacity (BCIKS) and
  mutual-correlated-agreement-up-to-capacity (WHIR) conjectures are FALSE**. The corrected
  statements go only up to the **list-decoding-capacity boundary** `H_q^{-1}(1−ρ)`, NOT the
  rate `1−ρ`.
- Their **negative constructions use the smooth-domain structure**: Thm 1.6 over F₂-linear
  domains; the prime-field limitations (§1.4.3, Conj 1.12) use multiplicative subgroups +
  sumset growth. **Smoothness of μ_n is currently a source of COUNTEREXAMPLES, not positive
  bounds** — a serious warning for any "(R) holds" hope.

**Kumar–Ron-Zewi survey (arXiv:2603.03841, 2026):** explicit beyond-Johnson list-decoding of
plain fixed-domain RS is "a major open problem" with ZERO positive results. Capacity is reached
ONLY by folded/multiplicity (subspace-design) or random/random-puncture RS. JH01/BSKR06 give a
partial LOWER-bound obstruction (some RS need large list strictly between Johnson and δ).

## THE THREE UNWORKED SURFACES ARE ALL VACUOUS (prize-regime arithmetic, n=q^{1/4}=2^32)

1. **Kong–Tamo point-variety incidence (arXiv:2408.10977).** Spectral (expander-mixing) bound
   `|I−|P||V|/q^d| ≤ q^{n/2}√(|P||V|)·…`. Two fatal mismatches: (a) `S_w` (image of a Hamming
   ball under H) is NOT a function-graph variety in their class; (b) a single `q`-point line vs
   a single target is the bound's worst case. The companion **Tamo (arXiv:2312.12962) Thm 5.1**
   IS the RS instantiation — and it tops out at **Johnson** `1−√R` (the error term is a
   domain-AGNOSTIC `√(|L||P|·Q)` quantity with NO character-sum factor, so it cannot exploit
   smoothness). Vacuous for (R) by ~`q^{10⁹}`.
2. **Finite-field Littlewood–Offord** for `γ↦wt(s₀+γs₁)`. Right shape, but all LO/small-ball
   results (Tao-Vu, Nguyen-Vu, Halász) need GENERIC coefficients; here `s₁` is near-code
   (structured) — the inverse-LO regime where anti-concentration FAILS. Needs a NEW
   direction-sensitive inverse-LO theorem. None exists.
3. **Intermediate deep-holes / sumset structure of μ_n.** The honest frontier (BCHKS Conj 1.12),
   but the character-sum technology is ~10⁸ orders too weak and currently yields counterexamples.

## CHARACTER SUMS AT THE PRIZE THRESHOLD ARE TRIVIAL

di Benedetto et al (arXiv:2003.06165) Thm 3.1: for `q^{1/2} > |H| > q^{1/4}`,
`B(H) ≤ |H|^{1−31/2880}`. At the exact prize boundary `|H|=n=q^{1/4}=2^32`: saves **0.34 bits**
(`2^{31.66}` vs `2^32`), and the theorem **degenerates exactly at `q^{1/4}`** (invalid below).
For `n < q^{1/4}` (larger fields q≈2^160) NO nontrivial single-character bound is known
(Heath-Brown–Konyagin / BGK barrier). The energy wall (`E ≲ n^{2.45}` MRSS, `n^{5/2}` HBK) is
2026-confirmed; nothing beats trivial for `n ≥ q^{2/3}`.

## MY COMPUTATIONAL FINDING (the structured adversary determines δ*, q-independently)

Faithful small smooth-domain RS (μ_n, exact list-decode each γ). Measured worst-case far-line
incidence / list profile, sweeping `q`:
- The structured (antipodal pencil `u₁=x^{n/2}` / nodal `x^k+γ/x`) adversary's δ* is
  **q-INDEPENDENT** (e.g. `a₂ = n/2+1` exactly at n=8 AND n=16, ρ=1/4; worst-case δ* identical
  across q ∈ {73…241} and {97…241}). Random directions sit at the trivial agreement `k+1`.
- The structured δ* sits **strictly between Johnson and capacity** (n=16: ρ=1/4 → δ*≈0.625 vs
  Johnson 0.5, capacity 0.75; similar at ρ=1/2,1/8,1/16). The gap to Johnson is a q-independent
  STRUCTURAL quantity — the concrete realization of the BCHKS counterexample mechanism on μ_n.

This confirms the corrected picture: **δ* is pinned by the explicit algebraic adversary's
list-decoding radius (q-independent, char-0), strictly below rate-capacity.** The "average-term"
conjecture `δ*=H_q^{-1}(1−ρ−log_q(1/ε*)/n)` is an UPPER bound on δ* that the structured adversary
does NOT achieve (worst < average by the structural gap) — consistent with BCHKS disproving the
capacity conjectures.

## HONEST STATE FOR THE PRIZE

The prize δ* = the explicit-μ_n-RS list-decoding radius for list ≤ `q·ε*=n` (BCHKS equivalence).
The closed form is the structured-adversary radius (computable, q-independent), but proving it is
the EXACT value (the optimality = nothing beats the algebraic family) IS the recognized open
problem, with the smooth structure currently giving counterexamples not bounds. No accessible
technique (incidence/spectral, energy/character-sum, LO) discharges it. The genuinely-new input
required: a direction-sensitive inverse-Littlewood–Offord / beyond-Johnson explicit-RS
list-decoding theorem. DO NOT fabricate closure.

## ADDENDUM — generic μ_n smoothness is NEUTRAL (smooth ≈ random), the adversary is near-code

Decisive crux measurement (smooth vs random domain, matched params, max structured-adversary
incidence at the window radius, exact):
- n=12, k=3, agreement≥4: μ_n incidence 473 vs random 480 (ratio 0.99)
- n=16, k=4, agreement≥6 (=Johnson): μ_n incidence 22 vs random 23 (ratio 0.96)

**Generic μ_n smoothness is NEUTRAL** (ratio 0.96–0.99, marginally BELOW random). The
structured adversary's power comes from being NEAR-CODE (domain-independent: a near-code u₁
gives the same incidence over any domain), NOT from the domain's smoothness. This nuances the
"smoothness gives counterexamples" reading: the BCHKS counterexamples require a SPECIAL
structure (Thm 1.6 is F₂-linear; the prime-field limitations need a specific sumset-growth
admissibility, Conj 1.12), NOT generic multiplicative-subgroup smoothness. So at near-Johnson
radii a GENERIC μ_n is no worse than random — consistent with δ* being controlled, but the
DEEP-window regime (where the special structures could bite) remains the open question. Neither
closes nor refutes the prize; it localizes the danger to special structures + deep radii.

## REFINEMENT (self-correction) — the capacity-deficit is REAL but SMALL and STRUCTURED, measured

The incidence-genericity dichotomy in its clean form is REFINED by the across-window test
(refute-or-confirm, smooth vs random worst-case incidence at every window radius, ρ=1/4):
- n=12: at d=0.583 (deep window) smooth=4 vs random=0 — SMOOTH EXCEEDS (by 4).
- n=16: smooth≈random at all radii (2373/2369, 23/23, 0/0).
- n=20: at d=0.650 smooth=40 vs random=35 — SMOOTH EXCEEDS (by 5).

So smooth ≈ random at MOST radii, but the smooth domain carries a SMALL STRUCTURED EXCESS (the
algebraic/antipodal family: a few extra bad scalars) at specific DEEP-window radii where random
has dropped off. The excess is small (4–5) and roughly CONSTANT across n (12→20), NOT exploding.
**This directly MEASURES the capacity-deficit: it is real but small + structured**, consistent
with the master conjecture's `δ* = 1−ρ·N_fib(n,r)/N_fib(n,r−1)` (slightly sub-capacity, the
antipodal cost) rather than the pure average-term `H_q^{-1}` (which the excess sits just below).
Open question (the wall, unchanged): does the structured excess stay sub-`q·ε*` in-regime (prize
survives at the small-deficit δ*) or grow (catastrophic)? The N_fib closed form predicts it stays
small; proving it is the `PrizeFloorStatement` / Shkredov wall. Net: the workbench's
`prizeDeltaStar` (entropy ceiling) is the upper envelope; the true `δ*` sits a small structured
deficit below it, pinned by the antipodal `N_fib` count — the open core is exactly that the
deficit is the N_fib value and no larger.

## FLOOR-ATTACK WORKFLOW (4 angles, adversarially verified) — conjecture HEALTHY, wall exactly mapped
HEADLINE (Angle 3): prizeDeltaStar NOT refuted on prime-field dyadic domain — BCHKS catastrophic n^tau counterexample is CHAR-2-ONLY; BCHKS prime-field construction IS the in-tree antipodal ladder, incidence exceeds B=n only ABOVE the floor; measured deficit (4,0,5) = antipodal family = BCHKS sumset, O(1) constant-in-n. Open core (Angles 1+2): E(mu_n)=n^{2+o(1)} subgroup additive energy / uniform sqrt-cancellation; pair layer frozen (moment_identity_base) caps at EXACTLY Johnson, floor needs the >=3-wise moment N_{k+1}(w). NOVEL (Angle 2): char-0 moment route fails at r>=5 by PRIME-INDEPENDENT PIGEONHOLE (n^5>p forces spurious vanishing sums, no NTT prime escapes); clean r<=4.2, beats budget only r>=5, optimal r~116 (28x gap). (Angle 4) antipodal/Mobius symmetry = EXACTLY exponent-halving (WitnessLayerCount C(s/2-1,s/4)) + const, does NOT touch e^{Theta(n)} rate gap. NET: conjecture healthy; PrizeFloorStatement = recognized subgroup-energy wall, untouchable by pair layer / char-0 higher moments / structural symmetry. New input required = sqrt-cancellation for incomplete Gauss sums over mu_{q^{1/4}}; does not exist. No fabrication.

## SHARP IMPOSSIBILITY — no additive-moment route (any order) can prove the floor
(1) ENERGY/2nd-moment route is UNCONDITIONALLY short by n^{1/2}: list <= sqrt(n*E), but E(mu_n)>=n^2
ALWAYS (diagonal a+b=a+b; verified n=4..16), so list >= sqrt(n*n^2)=n^{3/2} > n=B regardless of the
energy bound. The sqrt-loss is a HARD n^{1/2} deficit vs budget, not just sub-Johnson. The entire
additive-energy programme (Shaw operator, char-sum 4th moment, all E(mu_n) bounds) caps at Johnson,
CANNOT reach the floor. (2) Higher moments r>=3 fail F_p transport by prime-independent pigeonhole
(n=q^{1/4}, n^r>p for r>=5 forces spurious vanishing sums, no NTT prime escapes), exactly at the order
the bound would beat budget. CONSEQUENCE: PrizeFloorStatement is provably beyond the whole additive-
moment hierarchy; it requires a fundamentally NON-moment argument (direct list-decoding / inverse-LO),
which does not exist. Stop seeking a better E(mu_n) bound for the floor — provably hopeless. probe
scripts/probes/probe_sqrt_loss_impossibility.py. The closed conjecture prizeDeltaStar stands (healthy);
its proof is this recognized, now-sharply-characterized wall.