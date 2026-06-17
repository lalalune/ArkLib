# The conjecture trichotomy: why every off-wall route to δ\* reduces to the BGK wall (#444)

**Date 2026-06-17. Status: a meta-theorem (strongly evidenced, partially formalized) — not a closure.**

This document records the central structural finding of the proximity-prize conjecture campaign. After **~150
conjectures** (the #407/#444 history) including **75 generated-and-attacked in this session across three rounds**
(a generic round, a fresh-machine round, and a full *iterative-hardening* round that produced 25 conjectures
surviving cursory refutation), the survivor count is **0**, and the *reason* is now sharp enough to state as a
trichotomy.

## The object

`M(μ_n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n` the order-`n` (`n=2^μ`) subgroup of `F_p^*`,
`p ≡ 1 mod n`, prize regime `p ≈ n^4` (β=4). The prize is `M ≤ C√(n log(q/n))` with `C=O(1)`; SOTA is `n^{1-o(1)}`
(BGK). The structural facts that drive the trichotomy:

- **Flat spectrum / Parseval.** `Σ_{b≠0}|η_b|² = pn − n²`, so the per-frequency RMS is exactly `√n`. The prize is
  the `√(log)` gap between this average and the worst-case sup.
- **Sidon-except-negation, 0-dimensional.** The only additive relation among elements of `μ_n` is the antipodal
  `x + (−x) = 0`; the additive-energy / relation variety is **0-dimensional** (in fact the genuine 3-term variety
  `{x₁+x₂=x₃}` is *empty*).
- **One exchangeable Galois orbit.** The `m=(p−1)/n` period values are a single Galois orbit of the totally-real
  subfield, exactly exchangeable (`Cov = −σ²/(m−1)`), light-tailed, with `disc(Ψ) = p^{m−1}f²` class-field-fixed.
- **Zero entropy.** The dilation `x ↦ hx` on `μ_n` is a single `n`-cycle (discrete spectrum, no mixing).

## The trichotomy

> **Meta-theorem (empirical, 75/75 + the in-tree necessity theorem).** Every conjecture proposed to bound `M`
> (equivalently to pin δ\* beyond Johnson) falls into at least one of three buckets:

**B1 — second-moment blind.** The method's *output* is an `L²`/average/total-mass/direction-averaged quantity. By
Parseval this is the scale `√n` (or `p`), and it is *structurally blind* to the `L^∞` sup, which needs the extra
extreme-value `√(log)` factor. **Obstruction (formalized):** a fixed-second-moment (flat) spectrum can have an
arbitrarily large maximum — the 2nd moment is invariant under collapsing all mass to one coordinate.
- Landed: `_AttackAN2_TightFrameBTVacuous` (the period frame is *exactly tight*, `S = pI − J`, two-point spectrum, so
  Bourgain–Tzafriri / restricted-invertibility / RIP are vacuous); `_AttackAN5...`/`isotropy_does_not_bound_sup`
  (isotropy / John-ellipsoid is a 2nd-moment certificate); `_AttackE2_MomentConeSpikeNoGo` (the `{S1,S2,S4}` moment
  cone admits a spike `S4^{1/4} ~ n^{5/4}`). Also kills: LP/Delsarte, SOS, Brascamp–Lieb/4th-moment, large-sieve,
  Nehari (bounds the operator norm = wrong object), Cheeger/Plancherel.

**B2 — BGK-rename.** The conjectured object *is* the Gauss-period / Cayley-graph spectrum / additive-energy ladder
under a new name; the "bound" is literally `M` itself or the open char-`p` excess `W_r`. **Obstruction (formalized):**
the Cayley adjacency eigenvalues *are* the `η_b` exactly, and an abelian Cayley graph of growing degree is not a
Ramanujan expander.
- Landed: `_AttackR2_AbelianCayleyNonRamanujan` (Cayley spectrum = `η_b`; `2√n` refuted, violation grows);
  `_AttackR6_RelationVarietyBezoutNoGo` (the relation variety counts `E_r`, not the excess); `_AttackT1`/`_AttackD6`.
  Also kills: Weil-rep matrix coefficients, transfer operators, Dudley chaining, motivic regulator, crystalline
  Newton-slopes (= Gauss sums), L-function/Chebotarev, the distinct-tuple variety (= the energy).

**B3 — Sidon-0-dim hypothesis failure.** The machine *requires* a structure `μ_n` provably lacks. **Obstruction
(formalized):** the relevant relation varieties are 0-dimensional/empty, and the relevant group cohomology vanishes.
- Landed: `_AttackRT6_CyclicSchurMultiplierNoGo` (`H²(Z_n,ℂ*)=0`, so a Drinfeld/quantum-group twist is a coboundary
  that preserves the spectrum); `_AttackB1_BadSetCosetNonSidon` (the bad set is a union of cosets, the opposite of
  Sidon); the empty 3-term variety (AN6). Also kills: decoupling/restriction (need curvature), Bourgain–Gamburd
  (need product growth, but `S·S=S`), Salem–Zygmund (need randomness), genus-reduction (the monomial curve is
  genus 0), Katz rigidity (not rigid), negative-association (fails for the periods).

### To escape, a conjecture must *simultaneously* satisfy

- **E1**: its output is the actual `L^∞` sup `max_b|η_b|` (not an average / 2nd moment / total mass);
- **E2**: its object is genuinely new (not `η_b` / the Cayley spectrum / the energy ladder renamed);
- **E3**: its hypothesis holds on the 0-dimensional, flat-spectrum, Sidon-except-negation, exchangeable,
  zero-entropy `μ_n` at β=4.

The empirical content of the campaign is that **E1∧E2∧E3 forces the conjecture to be the BGK sup-norm bound itself**:
a method that outputs the genuine sup (E1) of a genuinely-new object (E2) whose hypothesis holds on this flat,
structureless, 0-dimensional `μ_n` (E3) has nothing to grip *except* the deep arithmetic equidistribution of the
Gauss phases — which is the wall. This is why the prize is a *barrier* and not merely an unproven lemma.

## Relation to the in-tree necessity theorem

The "no-method" direction has a formal anchor: `moment_ladder_exceeds_prize` (no moment method, at any depth,
reaches the prize target `√(n log(q/n))`), and `_EnergyRatioMonotoneReduction` (`ERM-at-r ⟺ M ≤ √((2r+1)n)`, so the
energy route *is* the sup-norm wall). The trichotomy generalizes this from "moment methods" to "all three buckets."

## Honesty / scope

This is a **meta-theorem about proof strategies**, evidenced by 75/75 refutations with exact mechanisms and anchored
by the formalized bucket-obstructions above. It is **not** a proof that the prize is false (the empirical `C ≈ 1.25`
oscillates without visible divergence; the prize is widely believed *true*), nor a proof that no proof exists (that
would itself require a model of all proofs). It says: **every route reachable by the campaign's generation —
including a targeted iterative-hardening loop and ~10 sophisticated "new machines" (rep theory, Bourgain–Gamburd,
Brascamp–Lieb, quantum groups, matroid invariants, Vinogradov mean value, Dudley chaining, VC-dimension) — reduces
to B1∨B2∨B3, hence to the BGK/Paley wall.** Winning the prize requires a genuine analytic-number-theory breakthrough
on effective thin-subgroup Gauss-phase equidistribution at β=4 that evades all three buckets; no such idea is in the
literature or has been produced by the campaign.

## Constructive confirmation: targeted bucket-evasion yields 0 evaders (22/22)

A workflow tasked 5 expert generators to CONSTRUCT conjectures that provably evade all three buckets (output the
sup E1, genuinely new object E2, hypothesis holds on 0-dim Sidon mu_n E3). It produced 22 candidates (referee+attack
phases then hit the session usage limit; the referee was completed inline, anchored by an exact probe: period
RMS=sqrt(n) exactly, sup/RMS=2.26-2.49 = the open sqrt-log gap, and negative-association FAILS — pairwise indicator
covariance +0.013>0 at n=16). EVERY candidate falls in a bucket:

B1 (2nd-moment blind): E54 operator-Bernstein (commuting dilations -> scalar, uses variance); E55 Shannon capacity
(mutual info=average); E1-4 amplified large-sieve (=2nd moment); E1-6 Frobenius gap-statistic (T=(pn)I-nJ two-point
spectrum, trivial); E4b Suen/Janson tail (uses mean+pair-correlation); E4c & E2-3 Beurling-Selberg majorants (LP,
L1=Parseval); E2-2 hinge/first-moment (L1 average); E2-5 histogram entropy (average functional).
B2 (BGK-rename): E51 discrepancy-majorant & E52 optimal-transport edge (Erdos-Turan: discrepancy/W_1 = the character
sum eta_b); E1-1 finite-monodromy Deligne-Katz (distribution not effective sup); E2-1 large-spectrum count (= the
large-values/moment object); E4d Plotkin/anticode sign-code (= far-line Plotkin proxy/2nd moment).
B3 (Sidon-0dim hypothesis-fails): E53 skew-product mixing-edge (dilation=zero-entropy single n-cycle, no mixing);
E56 Pila-Wilkie (period set is ALGEBRAIC not o-minimal/transcendental, self-flagged partial); E1-2 Slepian-via-rank-1
-covariance & E2-4 exchangeable-Hoeffding & E4a NA-max-domination & E4e Stein-exchangeable-pair (periods are
DETERMINISTIC not a Gaussian/random process, and negative-association FAILS by probe); E1-3 conductor-discriminant
(disc CFT-fixed=house-blind); E1-5 l-adic cohomology-dimension (self-declared NO-GO, house-blind).

So even generation EXPLICITLY AIMED at the escape conditions cannot produce a single bucket-evader: 22/22 fall in
B1/B2/B3, two generators self-declared no-gos. This is the strongest constructive evidence that the trichotomy is
tight -- E1 (output the sup) + E2 (new object) + E3 (hypothesis holds on flat 0-dim Sidon mu_n) is jointly
unsatisfiable except by the BGK sup-norm bound itself.
