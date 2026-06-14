# The supply-explosion landscape at production smooth μ_n (pre-registered, #389)

Lane: nubs census/incidence seat (claim #389 comment 4697254276). The sub-Johnson supply
wall = max over (e₁..e_{m+1}) targets of the μ_n symmetric-function fiber at band t=k+m+1
(via EsymmFiber.explainable_iff_forcedPoly_degree). Two known explosion mechanisms:
multiplicative-subspace (coset unions = the all-zero target; production-vacuous, O158) and
Frobenius z^p subfield blowup (needs F_p-affine-closed domains). Pre-registered, falsify-first.

**H-MAX:** at fixed production ρ ∈ {1/2,1/4,1/8,1/16}, the MAX e-symm fiber over all targets
at band t=k+m+1 on μ_n is SUBEXPONENTIAL (log₂(maxfiber)/n → 0 as n grows). Falsifier: a
target with fiber 2^{Ω(n)}. [If confirmed: the supply wall holds at production ⟹ CensusDomination
plausible there.]

**H-EXT (inverse theorem):** every max-fiber extremizer's support is coset-union /
subfield-structured — "the known counterexamples are the only shape" (dossier §5 bet).
Falsifier: a large fiber with unstructured support (a new explosion mechanism).

**H-FROB:** the Frobenius z^p blowup requires F_p-affine-closed domains; production μ_n
(multiplicative, prime field, p≡1 mod n) is not affine-closed for n≥3 ⟹ immune. Falsifier:
a production μ_n admitting a p-rich affine secant family.

Synthesis target: if H-MAX ∧ H-EXT ∧ H-FROB hold, CensusDomination at production is a
candidate theorem; name the exact missing analytic brick.

## Verdicts (appended verbatim as the Opus-4.8 workflow lanes return)

### H-FROB — CONFIRMED IMMUNE (proven in-tree, was prose-only before this lane)

Exact in-tree hypothesis the Frobenius blowup needs: `AffClosed dom p`
(`FrobeniusSubfieldBlowup.lean:62`) — the domain IMAGE closed under 𝔽_p-affine
combinations. The Θ(n²) supply (`frobenius_supply_floor`, `frobenius_supply_exact`)
is gated on this and NOTHING else.

Before this lane the immunity claim was ASSERTED ONLY in prose
(`FrobeniusSubfieldBlowup.lean:37-39`); no Lean `¬ AffClosed (smoothDom …)` existed.
The Quarantine `Immunity.lean` "multiplicative_affine_immunity" is only an unproven
`def` (a Prop), char-2, not a theorem.

NOW PROVEN (axiom-clean: propext, Classical.choice, Quot.sound; compiles under
autoImplicit=false), file `Frontier/_FrobeniusImmunityMuN.lean` (artifact copy
`landscape/FrobeniusImmunityMuN.lean.artifact`):
  - `le_card_of_affClosed`  : `AffClosed dom p → i≠j → p ≤ n`
       (the 𝔽_p-line `secant hcl i j` has exactly p points, all in Fin n; reuses
        the existing `secant_card`).
  - `not_affClosed_of_card_lt` : `2 ≤ n → n < p → ¬ AffClosed dom p`.
  - `smoothDom_not_affClosed` : `μ_n = ⟨g⟩ ⊂ ZMod q (q prime), 2≤n<q → ¬ AffClosed (smoothDom g n hg) q`.

EXACT REASON (cleaner than the recon's Vieta framing): over a PRIME field
`F = ZMod q`, characteristic uniqueness forces `AffClosed` to be type-correct ONLY
at `p = q`; then a 𝔽_q-affine line through two points is the WHOLE field (q points),
so it cannot lie inside the n-point domain when n < q. A proper subgroup always has
`n ∣ q−1 ⟹ n < q`. So the secant family the blowup needs literally does not exist.

Probe `probe_frobenius_immunity_mun.py` (exact mod-q, exhaustive q ≤ 60, every
subgroup): zero AffClosed proper subgroups; every 𝔽_q-line through 2 μ_n points
= full field (|line| = q > n); and z^q = z on every prime field ⟹ the Frobenius
WORD itself degenerates to the identity codeword over a prime field (the blowup
fundamentally needs a PROPER subfield 𝔽_p < 𝔽_q, absent in production).

SCOPE / HONEST CAVEAT: this closes the FROBENIUS/AffClosed mechanism for prime-field
μ_n. It does NOT make μ_n immune to ALL supply blowup — DISPROOF_LOG 2026-06-12
(`MonomialSupplyWitness.lean`) shows μ_n carries Θ(C(n,t)/q^{m+1}) generic-density
supply at n=Θ(q) (e.g. 25.25·n cores on μ₄₀₉₆⊂𝔽₁₂₂₈₉). That is a DIFFERENT mechanism
(generic codim-(m+1) window, not affine lines) and is vacuous at production q ≥ 2^128
where q ≫ n. H-FROB is specifically about the AffClosed/subfield route, and on that
route production μ_n is now PROVABLY immune.

## Inline cross-check baseline (nubs, before workflow lanes — exact, for verification)
mu_16 in F_97, rho=1/2 (k=8): band offset m → (MAXfiber, all-zero-fiber, max@zero):
  m=0 t=9: (144, 64, NO)   m=1 t=10: (5, 0, NO)   m=2 t=11: (3, 0, NO)   m=3 t=12: (1,1,YES)
mu_16 in F_97, rho=1/4 (k=4): m=0 t=5: (61,16,NO)  m=1 t=6: (5,0,NO)  m=2 t=7: (3,0,NO)  m=3 t=8: (2,2,YES)
mu_8 in F_17, rho=1/2 (k=4): m=0 t=5: (4,0,NO) m=1:(1) m=2:(1) m=3 t=8:(1,1,YES)
NOTES for the lanes to resolve: (1) the m=0 band has max fiber = max subset-sum multiplicity
(144 = max over e_1 of #{9-subsets of mu_16 with that sum}) — this is the BOUNDARY band
(UniversalBoundaryBound: sup = C(n,k+1), known-bad); the OPEN deep band is where the pin's
floor a₀ sits — recon must map which m that is. (2) The max extremizer is NOT the all-zero
(coset-union) target except at the trivial top band — H-EXT needs refinement: at the boundary
band the extremizer is a NON-zero subset-sum target. (3) Lane B must report the GROWTH in n at
the pin's actual band, not the boundary band — these n=16 numbers are the anchor.

## H-FROB — VERDICT: CONFIRMED + PROVEN IN LEAN (2026-06-13, O159)
The Frobenius blowup's sole domain hypothesis is `AffClosed dom p`. Production immunity was
PROSE-ONLY in-tree (FrobeniusSubfieldBlowup.lean:37-39). Now proven, axiom-clean, in
`FrobeniusImmunityMuN.lean`: `le_card_of_affClosed` (AffClosed ⟹ p ≤ n via secant_card),
`not_affClosed_of_card_lt` (2≤n, n<p ⟹ ¬AffClosed), `smoothDom_not_affClosed` (production
μ_n ⊂ 𝔽_q, q prime, 2≤n<q is NOT 𝔽_q-affine-closed). So the Frobenius Θ(n²) blowup is
VACUOUS over every production smooth domain — the second explosion mechanism is now
PROVABLY production-blocked (the first, coset-union, was O158). Reason: an 𝔽_q-affine line
has q points, q>n.
## H-MAX / H-EXT — IN PROGRESS (workflow lanes capped at session limit, resuming inline)
