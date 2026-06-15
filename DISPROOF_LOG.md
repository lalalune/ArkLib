# DISPROOF / NO-GO LOG (#407 and predecessors)

Machine-checked refutations and precise pins. Each entry: lens, test, exact result, wall.

## BIND-gate-scope — the §5.0 (BIND)/house gate route does NOT generalize: non-antipodal mod-p vanishers EXIST at thin prize-β primes once (#S)^φ > p (2026-06-15)

Lens: §5.0 reduces CORE to (BIND) — "no spurious non-antipodal vanishing `Σ_{i∈S} ω^i ≡ 0 (p)` with S
not antipodal" — and proves it via the height gate `HeightGateNormBound.gate_2power_antipodal`, whose
HYPOTHESIS is `hp : (#S)^φ(n) < p` (house bound `|N(β)| ≤ (#S)^φ < p`, then `p|N ⇒ N=0 ⇒` antipodal).
The body claims "NoSpuriousVanishing is a proved theorem for n≤32" + "realized-height extends to n≤64,
heuristically n≤96", and frames the open part as "need a structure-aware norm bound (not trivial house)
to get |N|<p at n≥112."

TEST 1 (worst-case realized norm vs the fixed prize budget p~2^128). Hill-climbed max over reduced
coeff vectors c∈{-1,0,1}^{n/2} (the worst non-antipodal residue pattern; exact integer norm via
`Res(x^{n/2}+1, c(x))`, cross-checked high-precision):
  n=64:  max log2|N| = 78.9  (< 128, closeable — matches H(64)<2^128)
  n=96:  max log2|N| = 131.1 (> 128)
  n=112: max log2|N| = 160.5 (> 128)
  n=128: max log2|N| = 188.0 (> 128; vs ABF p~2^136 still >)
Growth ~0.184·n·log2(n) (a CONSTANT fraction ~37% of the house (n/2)log2(n/2) — the house slack does
NOT vanish). CROSSOVER between n=64 and n=96. The single 56-element witness cited in §5.0 (2^131) is
NON-worst-case; the true worst at n=96 already exceeds p. (scripts/probes/issue407-bind/probe_bind_realized_norm_max.py,
probe_bind_norm_crossover.py)

CONSEQUENCE: a "structure-aware UPPER bound giving |N|<p" CANNOT exist at the worst-case binding
weight for n≥96 — the realized worst-case norm itself exceeds p. The §5.0 open-route as stated
("replace the loose house by a tighter |N|<p") is a no-go past the crossover.

TEST 2 (the mechanism is real: explicit, INDEPENDENTLY-VERIFIED non-antipodal mod-p vanishers at thin
prize-β primes). For thin primes p (p>n^3, n|p-1, β=log_n p in the prize band 4–4.8) we exhibit
non-antipodal S with `Σ_{i∈S} ω^i ≡ 0 (mod p)` (ω a primitive n-th root in F_p), directly verified
(not via the bridge — the sum is computed in F_p and equals 0 on the chosen ω):
  • n=32,  p=14814881  (β=4.764): S={1,2,7,8,9,10,12,13,19,22,27} (#S=11), non-antipodal, Σω^i≡0.
  • n=64,  p=136085377 (β=4.503): #S=24 set, non-antipodal, Σω^i≡0.
  • n=128, p=268437889 (β=4.000): S={6,17,24,27,29,38,43,52,59,65,70,77,82,87,94,97,107,112,117}
    (#S=19), non-antipodal, Σω^i≡0; here house 19^64~2^272 ≫ p~2^28 (gate hyp `(#S)^φ<p` FALSE).
(scripts/probes/issue407-bind/probe_bind_counterexample_search.py + verify_bind_counterexamples.py
[standalone, from-scratch], probe_bind_n128_counterexample.py)

WALL / precise scope (NO prize refutation — honesty): these counterexamples use SMALL primes (p~2^24–2^28),
NOT the actual prize budget p~2^128, so the PRIZE is NOT refuted. What is refuted is the GENERALITY of
the gate route: (BIND) is FALSE as a ∀-thin-prime statement; non-antipodal vanishing genuinely occurs
exactly when `(#S)^φ(n) > p`. §5.0's "NoSpuriousVanishing proved for n≤32" is correct ONLY because at
the prize budget p~2^128 and n≤64 the house hypothesis `(#S)^φ < p` happens to hold for ALL relevant #S
(e.g. n=32: p^{1/φ}=2^8=256 > n). Once n grows so that (n/4)^{n/2} > 2^128 (i.e. n≥~112 at the binding
size), the house hypothesis fails AND — by Test 1 — no realized-norm replacement can rescue it. The
gate/house lane is therefore CAPPED at the crossover; closing CORE at n≥112 needs a genuinely different
mechanism (the thinness-essential B_∞←B_{log n} Sidon bootstrap), not a sharper norm bound on the gate.
Constraint lemma: `∃ non-antipodal S, ω prim. n-th root in F_p : Σ_{i∈S}ω^i=0` for every thin p with
(#S)^{φ(n)}>p — so the gate's safety margin is exactly `house < p`, nothing more.

## wf-NC — Gross-Koblitz / p-adic Γ_p refinement of Stickelberger (UNIT part) — PINNED (2026-06-14)

Lens: GK expresses g(χ^{−a}) = −π^a·Γ_p(⟨a/(p−1)⟩) (q=p prime ⇒ residue degree f=1);
η_b = (1/m)Σ_k ζ_{p−1}^{−nkc} g(χ^{nk}) is a ζ-weighted sum of GK factors. Hoped: dyadic
base-p digit-sum of a=nk + Γ_p reflection/multiplication ⇒ sub-trivial archimedean max_b|η_b|.
All numerics exact-as-float ~1e-14, n=8,16,32, multiple p≡1 (mod n).

- NC1 (f=1 single Γ_p factor): for q prime the GK product runs over the Frobenius orbit of size
  f=1 → ONE Γ_p factor per Gauss sum. No multi-factor product ⇒ the dyadic digit-sum handle is
  STRUCTURALLY ABSENT. The genuine multi-Γ_p / digit-sum lever needs f≥2 (q a prime power), which
  the prize forbids. (probe_wf2NC_gammap_valuation.py)
- NC2 (unit part has no archimedean SUP content): GK pins v_p(g)=a/(p−1) (=Stickelberger=section-6
  magnitude) and the unit Γ_p as a p-adic unit (|Γ_p|_p=1); |g|=√p is archimedean, independent of
  the unit congruence. Adversarial test (4000 trials): SUP achievable under the Γ_p reflection
  U(nk)U(−nk)=+1 EQUALS the SUP under |U|=1 alone (~0.86–0.95·√(p−n)); true SUP (0.58–0.79·√(p−n))
  sits strictly below, i.e. the genuine cancellation is NOT a GK relation. (probe_wf2NC_sup_vs_gk.py,
  probe_wf2NC_gk_phase.py)
- NC3 (no product→sum bridge): Davenport-Hasse/Stickelberger pin Π_k g(χ^{nk}) (= the norm/house,
  section-6 magnitude object), verified exact (rel.err ~1e-14); the SUP needs max_c|Σ_k ...|. A single
  product equation among m−1 unit phases does not bound a max-of-sum. (probe_wf2NC_gammap_valuation.py)

Why NEW (vs section-6 Stickelberger MAGNITUDE no-go): this is the complementary fact — the GK
unit/Γ_p part (the thing section-6 excludes) carries NO archimedean SUP info at f=1, and the only
digit-sum handle lives at f≥2 off the prize. The reflection formula reduces to the already-refuted
antipodal char-0 symmetry (T09-leak). Wall: GK adds nothing to max_b|η_b| for q prime.

## census<->CORE — the universal census bound is LOSSY, caps at Johnson, NOT equivalent to CORE (2026-06-14)

Lens: the count/census lane (`UniversalAlignmentLaw.badScalars_card_le_alignableSets`) bounds
`#{bad γ} ≤ #alignableSets(dom,k,a,u0,u1)`, feeding δ* via `epsMCA_le_of_alignableSets_card_le`.
#407 brief flags the "census ⟺ CORE equivalence" as ASSERTED-BUT-NEVER-PROVEN. Tested the tightness
directly: exact `#bad` (the CORE/incidence object) vs exact `#alignableSets` (census), thin proper
μ_16 ⊊ F_p*, large primes p≫n³, binding monomial direction u0=x^10,u1=x^4.
Probe: `scripts/probes/probe_407_census_core_tightness.py` (exact, no enumeration; left-null affine-γ).

- RESULT (p-INDEPENDENT across p=200017/500113/1000033):
  | r (a=n−r) | δ=r/n | #bad (CORE) | #alignableSets (census) | ratio |
  |---|---|---|---|---|
  | 8 (a=8) | .5000 | 9  | 10  | 1.11 |
  | 9 (a=7) | .5625 | 9  | 80  | 8.89 |
  | 10 (a=6)| .6250 | 89 | 456 | 5.12 |
  Budget = n = 16. **True δ* = 9/16** (#bad ≤ 16 through r=9, first bad r=10).
  **Census δ* = 8/16 = JOHNSON** (#alignableSets first exceeds 16 at r=9: 80 > 16).

- WALL / CONSTRAINT LEMMA: the census bound is **strictly lossy by a p-independent factor
  (5–9×) that turns on exactly at the beyond-Johnson rung**. Census `#alignableSets ≤ budget`
  fails at r=9 while the true incidence `#bad ≤ budget` holds, so **any δ* bound proven through
  the census/alignable-set count recovers at most JOHNSON (δ*=8/16), never the beyond-Johnson
  window**. The census overshoot = (every a-set that aligns for SOME γ is counted, but distinct
  aligned a-sets share γ's; `Aligned.gamma_eq` injectivity gives the ≤ direction but the reverse
  is many-to-one) ⟹ census counts aligned-sets, CORE counts γ's; the fibers have p-independent
  size 5–9 at the binding radii.
- THEREFORE: "census ⟺ CORE" is **FALSE**. Proving the count-lane bound (ExplainableCoreSupply /
  CensusDomination / SubJohnsonListBound) is NOT proving CORE in the prize window — it is a strictly
  weaker (Johnson-capped) handle. This is independent of, and complementary to, the §3 second-order
  cap (B5 already showed the count-lane is exponential-class, not second-order; THIS shows that even
  so, its δ* CERTIFICATE is Johnson-capped by the alignable-set overshoot). The beyond-Johnson rung
  is carried only by the γ-incidence (CORE/F2) count, which the census cannot see.

### census fiber structure (sharpening, 2026-06-14): fibers NON-UNIFORM (1..56), p-independent — census UN-repairable
Per-γ fiber size (# aligned a-sets a single bad γ owns), n=16 k=4, p-independent (p=200017/500113):
- r=9 (a=7): {8:×8, 16:×1} — total 80 over 9 γ.
- r=10 (a=6): {1:×16, 2:×64, 32:×8, 56:×1} — total 456 over 89 γ; max fiber 56.
The census overshoot is NOT a uniform constant — fibers range 1..56, a few heavy γ own huge fibers.
So census CANNOT be repaired into a CORE-tight bound by dividing by any fixed fiber size; the deflation
factor is itself a per-γ combinatorial quantity. Even the single worst γ is census-over-counted up to 56×.
The fiber-size multiset is a p-independent invariant of the binding configuration. Reinforces: the
count/census lane is Johnson-capped, cannot reach the prize window. (probe_407_census_core_tightness.py + /tmp/fiber.py)

## phase-alignment "tower self-similarity" — REFUTED, the alignment is just REALITY (2026-06-15)

Lens: the fleet observed at the worst frequency b* the two half-coset sums
S0(b*)=∑_{x∈μ_{n/2}} e_p(b*x), S1(b*)=∑_{x∈μ_{n/2}} e_p(b*·rep·x) are maximally phase-aligned
(cos=1.0000, machine-exact n=8,16,32,64). Floated as a candidate NON-AVERAGE structural handle
(tower-recursive self-similarity for a descent/Stepanov argument, since moment methods are blind
to worst-frequency alignment). Brief flagged this lane explicitly (phase-alignment tower probes).

Adversarial recheck (scripts/probes/probe_407_phase_dichotomy.py, probe_407_phase_why.py,
probe_407_phase_reality.py — all FFT-exact, ~1e-14):
- cos(S0(b),S1(b)) = ±1 for EVERY frequency b (256/256, 599/599 sampled), not just b*. The two
  half-coset sums are ALWAYS real-collinear.
- Holds IDENTICALLY in the THIN (β≈9.8, deep prize) AND THICK (β≈1.07, very thick) regimes. The
  cosine is ±1 everywhere; the sporadic −1 are sign flips of two REAL numbers, not a regime signal.
- ROOT CAUSE: μ_{n/2} is a 2-power cyclic subgroup of EVEN order n/2 ⇒ contains the unique order-2
  element −1 ⇒ closed under negation ⇒ S0(b)=∑ e_p(bx) is REAL (pair x↔−x). Verified
  max|Im S0(b)| ~ 1e-15. Two reals are trivially collinear ⇒ cos=±1 automatic.

CONSTRAINT LEMMA (axiom-clean Lean, Frontier/_PhaseAlignmentReality.lean):
`eta_real_of_neg_closed` — if G is closed under negation then eta ψ G b = ∑_{y∈G} ψ(b·y) is REAL
(conj-invariant) for every b. #print axioms ⊆ {propext, Classical.choice, Quot.sound}.

WALL: the "phase alignment" is forced by reality, holds for ALL b, and is identical in the thick
window where the prize is FALSE ⇒ it is NOT thinness-essential. Any descent built on cos(S0,S1)=±1
is thickness-monotone, which rule-3/§3 forbids. The alignment carries NO worst-frequency information
beyond "the half-coset sum is real," which is true unconditionally. Lane PINNED — not a non-average
handle.

## moment "count/Markov/EVT-tail" packaging is NOT sharper — one object in four costumes (2026-06-14)

Adversarial audit of the freshly-landed `MomentCountSupBound.forall_le_of_sum_pow_lt` (commit
64c0bc081), whose docstring claims the integer-tail-count argument is "SHARPER than the per-term
‖η_b‖^{2r} ≤ ∑ bound (it uses that a fractional count rounds down to zero)."

VERDICT: not asymptotically sharper. The count route certifies `a_b ≤ T` only under the STRICT
hypothesis `∑_b a_b^r < T^r`, i.e. for `T > Tᵣ := (∑ a^r)^{1/r}` strictly. The per-term route gives
the CLOSED bound `a_b ≤ Tᵣ` directly. Both families have the SAME infimal usable threshold `Tᵣ`; the
integer-rounding only discards the measure-zero boundary `∑ a^r = T^r`, never an asymptotic factor.

PROBE (scripts/probes/probe_407_count_vs_perterm.py, exact FFT, thin μ_n ⊊ F_p*, p~n^3.5-4): at EVERY
fixed r the per-term bound (∑ a^r)^{1/r} and the count-route infimal threshold coincide to machine
precision:
  n=8 β=4 p=4129:   r=2 830.41 / r=3 275.36 / r=5 125.96 / r=8 86.67  (per-term == count, all r)
  n=16 β=4 p=65537: r=2 6864.48 / r=3 1488.32 / r=5 504.80 / r=8 307.79 (equal, all r)
  n=16 β=3.5 p=16417: r=2 3428.51 / r=3 933.42 / r=5 376.79 / r=8 254.79 (equal, all r)

CONSEQUENCE: the direct ℓ^{2r}-root route (MomentSupNormBridge.sup_le_moment_root), the per-term root
(eta_le_optimized), the Markov tail bound (PeriodTailMarkov.card_filter_mul_le_sum_pow), and the
integer-count bound (MomentCountSupBound) ALL optimize the SINGLE object `min_r (∑_b ‖η_b‖^{2r})^{1/2r}`,
landing at the identical sqrt(n·log q)-gapped bound. Re-packaging the moment bound as a Markov tail /
integer count / EVT histogram does NOT escape the BGK √-cancellation wall. The EVT/tail-rate reframing
is the same analytic object in different costume; its open content stays `A_r ≤ Wick` (= BGK).

RIGOROUS Lean (MomentCountSupNotSharper.lean, axiom-clean {propext, Classical.choice, Quot.sound}):
- `forall_le_rpow_root`: the per-term CLOSED bound `∀ b, a_b ≤ (∑ a^r)^{1/r}` (count route not needed).
- `count_threshold_not_below_perterm`: for any `T < Tᵣ`, the count hypothesis `∑ a^r < T^r` is FALSE
  (`T^r ≤ ∑ a^r`), so the count route CANNOT certify a threshold below `Tᵣ`. Same infimum, no escape.

## DC-subtracted A_r<=Wick: CONFIRMED at prize DEPTH (r~ln q) for n=32..256 — ratio collapses, no catch-up failure (2026-06-14)

Follow-up confirmation of the 2026-06-14 ★★ correction (raw E_r<=Wick FALSE for n>=64; only the
DC-subtracted A_r = E_r - n^{2r}/q <= Wick is the correct prize input). The correction established A_r<=Wick
is "measured true" but did NOT publish the r-PROFILE at the prize depth r~ln q for n past the n=64 DC
crossover. Decisive question: does A_r CATCH UP to Wick at large r (the failure mode that killed raw E_r),
or stay below? Probe scripts/probes/probe_407_Ar_wick_depth_profile.py (exact FFT, thin mu_n subset F_p*,
p~n^3-4.5, A_r = (1/q) sum_{b!=0} |eta_b|^{2r}, Wick=(2r-1)!!*n^r):

| n   | p (q)     | r*=round(ln q) | A_r/Wick @ r=2 | @ r=4 | @ r=8 | @ r=r* |
|-----|-----------|----------------|----------------|-------|-------|--------|
| 32  | ~1.5e7    | 16             | 0.969          | 0.824 | 0.404 | 0.0156 |
| 64  | 16777601  | 17             | 0.984          | 0.908 | 0.710 | 0.119  |
| 128 | 14605697  | 16             | 0.992          | 0.946 | 0.647 | 0.0294 |
| 256 | 16777729  | 17             | 0.995          | 0.945 | 0.547 | 0.0051 |

VERDICT (confirmation, not closure): A_r<=Wick holds at EVERY depth through r~ln q, and the ratio A_r/Wick
DECREASES monotonically in r (0.99 at r=2 down to ~0.005-0.12 at the prize depth). So A_r is increasingly
BELOW Wick at the optimal order — the "A_r catches up to Wick at large r" failure mode (which killed raw
E_r via the DC term) does NOT occur for the DC-subtracted energy. The DC-subtracted reduction is robustly
non-vacuous with room to spare at prize depth across the prize-band n.

HONEST CAVEAT (why this is NOT the prize): these p are sub-prize (p~2^24, not 2^128), so this confirms the
r-profile shape and rules out the catch-up failure mode, but does NOT certify A_r<=Wick UNIFORMLY across
ALL fields at the actual prize budget — that uniform-in-field bound at depth r~log q IS the BGK wall (the
prize is forall-field-universal, c.154). The open content remains exactly A_r<=Wick as a thinness-essential
forall-field theorem. Value: pins the correct object's empirical r-profile (collapsing ratio), strengthening
confidence that the DC reduction is the right target and quantifying the numerical slack at prize depth.

## moment-certificate SLACK is THICKNESS-INVARIANT — the moment route cannot be the rule-3 thinness-essential lever (2026-06-15)

WALL / CONSTRAINT (rule-3 mapping). The DC-subtracted moment chain certifies the sup-norm via
`M(n) = max_{b!=0}|eta_b| <= min_r (q*A_r)^{1/2r}` (the moment certificate; `q*A_r = sum_{b!=0}|eta_b|^{2r}`).
Two facts were already known: (a) `A_r<=Wick` is measured-true at prize depth with collapsing ratio
(prior entry), and (b) the count/Markov/EVT-tail packagings are one object min_r(q A_r)^{1/2r} "in four
costumes" (not sharper). MISSING test: is this object **thinness-essential**? Rule 3 says any valid CORE
proof's certifying inequality must be FALSE in the thick window (beta~2.3-3.2) and TRUE only in thin
(beta~4-5). A thickness-INVARIANT certificate quality therefore CANNOT be the prize lever.

PROBE (scripts/probes/probe_407_Ar_thinness_essential.py, exact FFT over PROPER mu_n < F_p^*, beta swept
ACROSS the thick AND thin windows; cert = min_r (q A_r)^{1/2r}, true = M(n)):

| n  | beta (p)       | A_r<=Wick? (A_r/Wick @ r~lnq) | M/sqrt(n) | target sqrt(log(p/n)) | cert/true |
|----|----------------|-------------------------------|-----------|-----------------------|-----------|
| 8  | 2.27 (113)     | YES (0.049)                   | 1.808     | 1.627                 | 1.197     |
| 8  | 2.71 (281)     | YES (0.053)                   | 2.146     | 1.887                 | 1.181     |
| 8  | 3.20 (769)     | YES (0.040)                   | 2.430     | 2.137                 | 1.159     |
| 8  | 3.60 (1777)    | YES (0.051)                   | 2.547     | 2.324                 | 1.185     |
| 8  | 4.00 (4073)    | YES (0.023)                   | 2.665     | 2.497                 | 1.169     |
| 8  | 4.50 (11593)   | YES (0.009)                   | 2.714     | 2.698                 | 1.187     |
| 16 | 2.30 (593)     | YES (0.033)                   | 2.110     | 1.901                 | 1.210     |
| 16 | 2.70 (1777)    | YES (0.096)                   | 2.715     | 2.170                 | 1.173     |
| 16 | 3.00 (4129)    | YES (0.045)                   | 2.785     | 2.357                 | 1.171     |
| 16 | 3.30 (9377)    | YES (0.043)                   | 3.043     | 2.525                 | 1.153     |

TWO VERDICTS:
1. `A_r<=Wick` holds in BOTH the thick AND thin windows (ratio 0.03-0.10 thick, 0.009-0.023 thin) =>
   `A_r<=Wick` is NOT thinness-essential. It is honest substrate, true with room to spare across all beta.
   The thinness CANNOT live in the input inequality A_r<=Wick.
2. **The moment certificate's SLACK `cert/true = (min_r (q A_r)^{1/2r}) / M(n)` is THICKNESS-INVARIANT,
   locked at 1.15-1.21 across the ENTIRE beta window (thick 2.27 -> thin 4.5) and across n=8,16.** The
   moment route overshoots the true sup-norm by a constant ~18% that does NOT depend on thinness. Since the
   certificate quality is beta-uniform, the moment family (energy/Wick + count/Markov/EVT-tail, all four
   costumes) CANNOT be the rule-3 thinness-essential mechanism: a thickness-monotone certificate cannot
   prove a bound that is FALSE in the thick window. Any beta-aware refinement of A_r<=Wick is ruled out as
   a prize lever -- the residual ~18% slack lives in the moment->sup passage M<=(q A_r)^{1/2r}, and that
   passage's loss is regime-uniform.

WHERE THIS LEAVES THE OPEN CONTENT (mapping, not closure): not in tightening A_r<=Wick (beta-uniformly
far below Wick), not in the moment->sup step (beta-uniform constant slack). Corroborates "one object in
four costumes": the WHOLE moment family is beta-uniform, hence rule-3-incompatible standalone. A genuine
CORE proof must use a thinness-DISCRIMINATING object whose certifying inequality flips sign between the
thick and thin windows -- the moment certificate provably is not such an object.

HONEST CAVEAT: small-n / sub-prize p (p<=~12k, not 2^128); this maps the certificate's regime-behavior
shape, it does NOT itself prove or refute the prize. No Lean theorem claimed (the thickness-invariance is
an empirical measurement; proving the constant-slack would itself require BGK). Reproducible probe + this
constraint entry are the deliverable, per rule 4 (a precisely-mapped wall is a WIN).

## thinness-discriminator search: normalized prize-ratio R and shallow Sidon-depth are NOT decisive rule-3 discriminators (2026-06-15)

CONTEXT. Prior entry (82581fb79) showed the moment certificate is thickness-INVARIANT, so the prize
lever must be a thinness-DISCRIMINATING object (certifying quantity bounded in thin beta~4-5, ill-behaved
in thick beta~2.3-3.2). This entry tests the two most natural candidates and finds NEITHER is a clean
discriminator at accessible scale -- narrowing where the real lever can live.

PROBE (scripts/probes/probe_407_thinness_discriminator.py, exact FFT/enumeration, proper mu_n<F_p^*):

D1 -- normalized prize ratio R(n,p) = M(n)/(sqrt(n)*sqrt(log(p/n))) (prize wants R<=C absolute):
| n  | beta | R      |          | n  | beta | R      |
|----|------|--------|          |----|------|--------|
| 8  | 2.27 | 1.111  |          | 16 | 2.30 | 1.110  |
| 8  | 2.71 | 1.137  |          | 16 | 2.70 | 1.251  |
| 8  | 3.20 | 1.137  |          | 16 | 3.00 | 1.182  |
| 8  | 3.60 | 1.096  |          | 16 | 3.30 | 1.205  |
| 8  | 4.00 | 1.067  |          | 16 | 3.60 | 1.152  |
| 8  | 4.50 | 1.006  |          |    |      |        |
  n=8 avg R: thick(beta<3.3)=1.129, thin(beta>=3.9)=1.037 -- mild thin-TIGHTENING toward ~1.0.
  n=16: R is NON-monotone, stays ~1.10-1.25 across all beta (no clean convergence; no thick blow-up).
  VERDICT: R is O(1) in BOTH regimes. The n=8 convergence to 1.006 at beta=4.5 is suggestive but is
  likely a small-n artifact (only n=8 reaches beta=4.5 cheaply); n=16 shows R bounded but NOT
  thin-converging. R is NOT a decisive rule-3 discriminator -- it does not blow up in the thick window,
  it just sits at a slightly higher O(1) constant there. (Consistent: sqrt(log(p/n)) is the right SCALE
  in both regimes up to a constant; the prize's open content is the absolute CONSTANT, not the scale.)

D2 -- shallow additive Sidon-depth signature (waste = 1 - distinct(r-fold sumset)/n^r; lower=more Sidon):
| n  | beta | r=2 waste | r=3 waste | r=4 waste |
|----|------|-----------|-----------|-----------|
| 8  | 2.53 | 0.484     | 0.8125    | 0.9607    |
| 8  | 4.00 | 0.484     | 0.8125    | 0.9451    |
| 16 | 2.49 | 0.496     | 0.8359    | 0.9846    |
| 16 | 4.00 | 0.496     | 0.8281    | 0.9560    |
  VERDICT: r=2 and r=3 waste are IDENTICAL thick vs thin (field-blind) -- the shallow additive structure
  of mu_n is determined by n, not p (consistent with brief's "mu_n is B_inf-Sidon to depth ~log n"
  regardless of field). Only at r=4 does thin show modestly less waste (more distinct, 0.945 vs 0.961
  n=8; 0.956 vs 0.985 n=16) -- the depth where small thick-p starts forcing extra collisions. So shallow
  Sidon-depth is NOT a thinness discriminator; any signal would be DEEP (r ~ log n), exactly the
  inaccessible-by-enumeration regime that IS the B_inf <- B_{log n} bootstrap wall.

NET (mapping): the two natural discriminators both FAIL to cleanly separate thin from thick at accessible
scale -- R stays O(1) in both (the open content is the absolute constant, scale is right in both regimes),
and Sidon-structure is field-blind until depth r~log n (the inaccessible bootstrap regime). This narrows
the rule-3 lever: it must live at DEEP additive order r~log n (the B_inf<-B_{log n} bootstrap), not in any
shallow/normalized O(1) statistic -- consistent with the 25-yr wall being genuinely a deep-order phenomenon.

HONEST CAVEAT: small-n / sub-prize p; reproducible probe maps the discriminator candidates' behavior, does
not prove/refute the prize. No Lean theorem claimed. Per rule 4, a precisely-mapped non-discriminator is a WIN.

## K1 / antipodal-pairing residual H FAILS at the prize scale — derivable refutation (2026-06-14)

The in-tree GaussianEnergyFromPairing.gaussianEnergyBound_of_pairing derives the raw Wick carrier
GaussianEnergyBound G r (E_r <= (2r-1)!!*|G|^r) from three inputs: unconditional henergy (negation-closure
energy = zeroSumCount), unconditional hcount (#pairings <= (2r-1)!!), and the genuine open input H = the
ANTIPODAL-PAIRING RESIDUAL ("every zero-sum 2r-tuple of G is antipodally paired").

The 2026-06-14 ★★ correction (DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt) PROVES the
conclusion GaussianEnergyBound G r is FALSE when q*(2r-1)!! < |G|^r (the prize regime: n>=64 at r~log q,
DC term |G|^{2r}/q >> Wick). By modus tollens (henergy, hcount unconditional), H ITSELF IS FALSE at prize.

LANDED: PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt (axiom-clean
{propext, Classical.choice, Quot.sound}): under henergy + hcount, q*(2r-1)!! < |G|^r => NOT H, i.e. there
EXISTS a zero-sum 2r-tuple of G that is NOT antipodally paired.

INTERPRETATION (mapped wall): the above-threshold antipodal-pairing structure (true in char 0 / Lam-Leung
and at small n) is DESTROYED by the char-p anomaly at n>=64, r~log q. The non-antipodal zero-sum tuples
are exactly the char-p extra solutions the DC term counts (E_r >= |G|^{2r}/q >> Wick). So the K1 / pairing
route CANNOT supply the prize carrier E_r <= Wick at prize scale; only the DC-subtracted A_r <= Wick
survives (the genuinely thinness-essential object — consistent with the A_r r-profile confirmation note
above). The pairing/Lam-Leung char-0 route is prize-DEAD without DC subtraction; the bricks consuming raw
GaussianEnergyBound (GaussianEnergyFromPairing, GaussianEnergyThreeRepThree's r=3 rung) are vacuous /
have prize-false hypotheses at n>=64 exactly as eta_le_optimized is.

## SIGNED deep period-power cancellation IS thinness-essential — and the moment certificate's |.| destroys it (2026-06-15)

THE FIND (positive structural map, the missing rule-3 signal). Prior entries showed the moment certificate
min_r (q A_r)^{1/2r} is thickness-INVARIANT and shallow statistics are field-blind, leaving the rule-3
lever at deep additive order. This locates it: the SIGNED deep period-power sum.

Since mu_n is negation-closed, eta_b in R. Define the normalized signed deep sum
    C_r(n,p) = |sum_{b!=0} eta_b^r| / ((p-1) * M^r),   M = max_{b!=0}|eta_b|.
C_r=1 means no cancellation (all eta_b^r aligned); C_r->0 means strong signed cancellation across b.
(Note sum_{b!=0} eta_b^r is the deep additive structure: p*W_r/... = 1 + (1/n^r) sum_{b!=0} eta_b^r.)

PROBE (scripts/probes/probe_407_deep_sidon_depth.py + probe_407_signed_deep_cancellation.py, exact, proper mu_n):
| n  | beta | C_2   | C_4   | C_6   | C_8    | C_10   |
|----|------|-------|-------|-------|--------|--------|
| 16 | 2.49 | 0.210 | 0.116 | 0.081 | 0.063  | 0.052  |   (THICK)
| 16 | 4.00 | 0.084 | 0.020 | 0.0072| 0.0034 | 0.0019 |   (THIN)
| 8  | 2.53 | 0.214 | 0.113 | 0.081 | 0.066  |   -    |   (THICK)
| 8  | 4.50 | 0.136 | 0.048 | 0.025 | 0.016  |   -    |   (THIN)

THIN/THICK cancellation ratio (thick C_r / thin C_r), n=16: r2=2.5x, r4=5.8x, r6=11x, r8=18x, r10=27x.

VERDICT (thinness-ESSENTIAL, rule-3 compatible):
- C_r is strictly SMALLER (stronger signed cancellation) in THIN than THICK at EVERY r, and the thin/thick
  ratio GROWS with depth r (2.5x at r=2 up to 27x at r=10 for n=16). This is the deep-order, thinness-
  ESSENTIAL phenomenon rule 3 demands: a quantity whose behavior genuinely separates thin from thick and
  whose separation strengthens at the prize depth r~log n. Unlike A_r<=Wick (beta-uniform) and the moment
  certificate (thickness-invariant), the SIGNED period-power sum sum_{b!=0} eta_b^r carries the thinness.
- MECHANISM for WHY the moment route fails (closes the prior 'four costumes' map): the moment certificate
  uses sum_{b!=0}|eta_b|^{2r} (absolute values), which DESTROYS the signed cancellation. The thinness-
  essential content lives in the SIGNED sum sum_{b!=0} eta_b^r; taking |.| (as every moment/energy/Wick/
  count/EVT packaging does) discards exactly the cancellation that distinguishes thin from thick. THIS is
  why the moment family is thickness-invariant (prior entry) and cannot be the lever: |.| is the leak.

WHERE THE OPEN PRIZE LEVER NOW SITS (sharpened, positive): a bound on M must exploit the SIGNED deep
cancellation in sum_{b!=0} eta_b^r (which IS thinness-essential, growing with r), NOT the absolute moment.
This is consistent with the BGK/Stepanov flavor (signed/algebraic cancellation, not measure/energy). Any
method that passes through |eta_b| at any step is provably rule-3-incompatible (loses the thin signal).

HONEST CAVEAT: small-n / sub-prize p (<=65537); exact-verified at this scale. Maps the thinness-essential
object + the |.|-leak mechanism; does NOT prove a uniform-in-field deep-cancellation bound (that bound at
r~log q IS the prize/BGK wall). No Lean theorem (a quantitative signed-cancellation bound = the open core).
Reproducible probes + this constraint/structure entry are the deliverable. Rule-4 mapped-frontier WIN, and
unlike a pure wall this is a POSITIVE localization: the lever exists, it is the signed deep sum, and the
moment route's |.| is precisely why nobody saw it.

## Pairing-route rung boundary r*(n,q): char-p anomaly invades the K1/pairing ladder at DESCENDING rungs (2026-06-14)

Sharpening of "K1/antipodal-pairing residual H FALSE at prize" (PairingResidualFailsAtPrize). For FIXED
prize (n,q), at which rung r does raw E_r <= Wick (=> H) FIRST fail? Probe
scripts/probes/probe_407_pairing_rung_boundary.py (exact FFT, E_r=(1/q)sum_all|eta_b|^{2r}, Wick=(2r-1)!!n^r):

| n   | beta | p        | r*=first r with E_r>Wick | DC-predicted r* | round(ln q) |
|-----|------|----------|--------------------------|-----------------|-------------|
| 32  | 4.5  | 5931649  | 15                       | 15              | 16          |
| 64  | 4.0  | 16777601 | 6                        | 7               | 17          |
| 128 | 3.4  | 14605697 | 4                        | 5               | 16          |
| 256 | 3.0  | 16777729 | 3                        | 4               | 17          |

The failing rung r* DESCENDS as n grows (15 -> 6 -> 4 -> 3), tracking the DC-crossover within ±1. So the
char-p anomaly invades the pairing/Wick ladder at progressively LOWER orders: at n=256 even r=3
(E_3/Wick=1.046) is prize-false. Consequence: the in-tree r=3 pairing rung GaussianEnergyThreeRepThree
(deriving GaussianEnergyBound G 3 from repThree) has a PRIZE-FALSE hypothesis for large n, just like
eta_le_optimized and the general H. Essentially the ENTIRE moment ladder above r=2 is pairing-dead at
prize scale (r* -> small as n -> infinity). Only the DC-subtracted A_r <= Wick survives at every rung
(confirmed separately: A_r/Wick collapses, never crosses 1). The char-0 Lam-Leung pairing structure is
not "loose at high r" but actively false from a low, n-shrinking rung onward — the DC subtraction is
the only repair. Reinforces: prize object = DC-subtracted A_r <= Wick, forall-field, = BGK wall.

## Anomaly-suppression in-window survival — bad primes INVADE the prize window (β_bad grows in n), but Anom_r ≤ n^{2r}/p STILL HOLDS there (2026-06-15)

LENS: the HEAD anomaly route (dbbe1b01e). `Anom_r(p) = E_r^(p) − E_r^(0) ≤ n^{2r}/p` is the SUFFICIENT
condition for `A_r ≤ Wick` (the DC-subtracted prize core). Orchestrator showed `Anom = EXACTLY 0` at n=8
prize primes (r≤6) and flagged the OPEN asymptotic: for large n the bad primes (where Anom>0) can reach the
prize window `[n^4, (2r)^{n/2}]` at r~log q.

TEST (exact, NEW angle = NORMS, no per-prime FFT for the onset):
`Anom_r(p) > 0  ⟺  p | N(α)` for some r-collision difference `α = Σζ^{a_i} − Σζ^{b_j} ≠ 0` in `Z[ζ_n]`.
So r-bad primes = prime factors of the norms `N(α)` (computed exactly via the φ=n/2 conjugate product,
ζ^φ=−1 for n=2^a). Probe `scripts/probes/probe_407_anom_badprime_norm_onset.py`.

RESULT 1 — bad-prime onset exponent β_bad = log_n(p_bad) GROWS in n, invading the prize window at LOWER r:
  n=8:  first r with p_bad ≥ n^4 is r=6 (β_bad 4.28)
  n=16: r=4 (β_bad 4.60)
  n=32: r=2 (β_bad 4.87)
=> the orchestrator's "Anom=0 at prize primes" is a SMALL-n ARTIFACT (at n=8 the window is bad-prime-free
below r=6). Matches the independently-observed pairing-rung descent (r* 15→6→4→3, b58cf1d03): the char-p
anomaly is NOT confined below the prize window asymptotically.

RESULT 2 — but the SUFFICIENT condition SURVIVES at the in-window bad primes (the real BGK test at scale):
n=16, r=4, ALL 26 in-window bad primes p ∈ [n^4=65536, 1.5e6]: `Anom_4(p) ≤ n^8/p` HELD at **26/26**,
TRUE WORST ratio = **0.4757** at p=76001 (β=4.053), i.e. ~2.1× margin. Probe
`scripts/probes/probe_407_anom_suppression_inwindow.py` (vectorized norms + exact FFT integer-count Anom).

NET (honest): a POSITIVE mapped-frontier result for the anomaly route — bad primes do invade the window
but the anomaly is suppressed there with margin at accessible scale. NOT a closure: sub-prize-budget primes
(p ≤ 1.5e6), fixed r; the worst PRIZE prime at r~log q, p~2^128 (the BGK content) is untouched. Complements
`probe_407_bgkproof_onset_growth` (which tracks the ratio along the r-axis at a fixed prime); this pins the
worst-case ACROSS the bad-prime set inside the window at fixed r. Both axes now bounded at accessible scale.

---

## [over-det δ*] s* budget-crossing: s*−k appears CONSTANT (=3) at accessible n — honest tension with floor (2026-06-15, opus-4-8 subagent)

Follow-up to the over-det incidence MAX closed form `I_max(n)=n³/32−n²/8+1` (push 0c7492b0d) and the
union-of-singletons p-independence brick (47dcd71b3, sibling). The δ* open item #2 is the budget-crossing
`s* = min{s : maxI(s) ≤ budget=n}`, giving `δ* = (n−s*)/n`.

PROBE (probe_407_sstar_budget_crossing.py, char-0 p≫n³, far-incidence COUNT per direction, s swept up
from k+2; MAX over directions; full-direction at n=16, antipodal-nbhd lower-bound at n=20):
- **n=16, k=2: s*=5 (FULL-direction verified — maxI(4)=97>16, maxI(5)=16≤16). s*−k=3. δ*=0.6875.**
- **n=16, k=4: s*=7 (antipodal-nbhd; matches the campaign's independently-published δ*=0.5625). s*−k=3.**
- **n=20, k=2: s*=5 (antipodal-nbhd ⟹ s* LOWER BOUND). s*−k=3. δ*=0.75.**

OBSERVATION: `s*−k = 3` is CONSTANT across n=16,20 AND k=2,4 in the accessible range — both k-independent
and n-independent here. This SHARPENS the prior `deltastar-407-char0-logn-over-n-candidate` note, which
conjectured `s*−k = log₂(n)` from only n=16,32 at ρ=1/8 (where log₂16=4, but my n=16 gives s*−k=3, not 4 —
the discrepancy is the budget/direction convention: my budget is exactly n, full-direction MAX).

HONEST TENSION (the decisive open question, NOT resolved here):
- IF `s*−k` stays constant → `δ* = 1 − (k+s*−k)/n → 1` (capacity) as n→∞, which would CONTRADICT the
  conjectured floor `δ* = 1−ρ−Θ(1/log n)` (a Θ(1/log n) gap BELOW capacity). i.e. constant-defect ⟹ δ*
  rises ABOVE the floor (toward capacity) asymptotically.
- BUT: this is exactly the doc's flagged pre-asymptotic regime (small n, coarse 1/n band granularity,
  the conjectured floor is itself below Johnson at these n = degenerate window). Constant-3 at n∈{16,20}
  CANNOT be extrapolated — n=32,64 (army's Rust engine, ~9.6h+ at ρ=1/4) is needed to see if s*−k grows.
- CAVEAT: my n=20 antipodal-nbhd s* is a LOWER BOUND (a non-antipodal direction could keep maxI above
  budget at s=5, pushing the true s* up). The constant could be an undercount artifact at n>16.

NET: a mapped data point (n=16 full-verified s*=5 ⟹ δ*=0.6875) + an honest tension (constant s*−k ⟹
δ*→capacity, contra the floor) that the army's large-n Rust must resolve. NOT a refutation of the floor
(small n, lower-bound s* at n>16). Logged, not receipted (over-det lane actively sibling-owned, 47dcd71b3 —
one-active-speaker; not crowding with a competing receipt).

## ★ REFINEMENT (sharpens the in-window survival entry above) — the SUFFICIENT proxy `Anom_r ≤ n^{2r}/p` FAILS at deep r at the worst prime, but the TARGET `A_r ≤ Wick` survives with margin (2026-06-15)

Combined-axes trajectory at the WORST in-window bad prime p=76001 (n=16, β=4.05), r=2..r*=round(log p)=7:
  r : Anom_r/(n^2r/p) [sufficient proxy] | A_r/Wick [actual target]
  2 : 0.000 | 0.936     5 : 0.870 | 0.517
  3 : 0.000 | 0.819     6 : 1.091 | 0.374  <-- proxy CROSSES 1
  4 : 0.476 | 0.671     7 : 1.188 | 0.255  <-- proxy > 1
So `Anom_r ≤ n^{2r}/p` (the clean sufficient form) FAILS at r=6,7 at the worst in-window prime — it does
NOT survive to the optimizer depth r*. The fixed-r=4 survival result (26/26) is correct but does NOT extend
to deep r at the worst prime.

CRUCIAL: the ACTUAL target `A_r ≤ Wick` HOLDS at EVERY r (0.94→0.67→0.52→0.37→0.26, monotone decreasing),
because `A_r ≤ Wick ⟸ Anom_r ≤ n^{2r}/p + (Wick − R_r)` and the `(Wick − R_r)` headroom absorbs the anomaly
overshoot at deep r. (Consistent with probe_407_bgkproof_onset_growth's decomposition.)

NET: the clean sufficient proxy `Anom_r ≤ n^{2r}/p` is the WRONG (too-strong) sufficient form at deep r — it
overshoots exactly where the moment optimizer sits. The true open object is `A_r ≤ Wick` directly (= the
DC-subtracted BGK core), which survives with margin at this accessible-scale prime but is NOT implied by the
clean Anom-proxy past r=5. Anyone trying to close CORE via `Anom_r ≤ n^{2r}/p` will hit this proxy-failure at
deep r; must use the `(Wick − R_r)` headroom (i.e. the full `A_r ≤ Wick`), not the clean proxy.
Probe scripts/probes/probe_407_anom_worst_rtraj.py.

## ★ POSITIVE reframing — `A_r/Wick` is MONOTONE-DECREASING & ≤1 in THIN, but EXCEEDS 1 & non-monotone in THICK ⟹ a base-case+monotonicity proof of `A_r ≤ Wick` is automatically THINNESS-ESSENTIAL (2026-06-15)

LENS: the genuine open prize object is `A_r ≤ Wick` (DC-subtracted, ∀-thin-field, r~log q = BGK). Candidate
reduction lever: `f(r) := A_r/Wick`. The C14 batch + my p=76001 trajectory both showed f monotone-DECREASING.
IF f(1) ≤ 1 (PROVEN: base_case_strict, A_1 < Wick) AND f(r+1) ≤ f(r), then `A_r ≤ Wick` ∀r by monotonicity.

TEST (exact FFT spectrum + integer cross-check, probe scripts/probes/probe_407_ArWick_monotone_thinness.py):
- THIN (prize, β 3.9-4.6, n=8,16,32): f(r) MONOTONE-DECREASING and ≤ 1 at EVERY r. Robust across n, β, p.
  (e.g. n=32 β=4.2 p=2097857: f = 1.00, 0.97, 0.91, 0.82, 0.71, 0.59, 0.46 — clean.)
- THICK: mostly monotone too, EXCEPT the maximally-2-structured n=32 in F_4129 (β=2.40, v₂=16): f RISES
  ABOVE 1 from r=2 (peak 1.705 @ r=5) and is NON-monotone. EXACT integer cross-check: E_2=3744, A_2=3490 >
  Wick=3072 (A_2/Wick=1.136) — `A_r > Wick` genuinely FALSE in that thick window.

NET (POSITIVE, rule-3-correct): the property "f(1) ≤ 1 AND f monotone-decreasing" HOLDS in thin and FAILS in
thick (f exceeds 1 + non-monotone). So a proof of `A_r ≤ Wick` via [base case f(1)≤1] + [single-step
monotonicity f(r+1) ≤ f(r)] is AUTOMATICALLY thinness-essential — any thickness-monotone method is ruled out
because the thick window violates BOTH ingredients. This REFRAMES the open core from the sup-norm / "A_r ≤ Wick
∀r" to the SINGLE-STEP monotonicity `A_{r+1}/Wick ≤ A_r/Wick` at r~log q. Still BGK-hard (the deep-r single
step IS the hard inequality), but a cleaner, rule-3-satisfying target than the sup-norm directly. NOT a
closure — the deep-r monotonicity step at the worst thin prize prime is the irreducible content; no Lean
theorem (proving the single step uniformly = BGK).

## ★ SHARPENING — the monotonicity step is the clean inequality `A_{r+1}/A_r ≤ (2r+1)n`; holds THIN with GROWING margin, fails THICK (2026-06-15)

Sharpens the A_r/Wick-monotonicity reframing above. The step f(r+1) ≤ f(r) is EXACTLY:
   A_{r+1}/Wick_{r+1} ≤ A_r/Wick_r  ⟺  A_{r+1}/A_r ≤ Wick_{r+1}/Wick_r = (2r+1)·n.       (STEP)
Since A_{r+1}/A_r is a |eta_b|^{2r}-weighted average of |eta_b|^2, A_{r+1}/A_r ≤ M^2; and (STEP) at r~log q
⟺ M^2 ≤ (2r+1)n ≈ 2n log q = the PRIZE. So (STEP) at deep r ⟺ prize (BGK-hard, confirmed).

MEASURED (exact FFT spectrum, g(r) = (A_{r+1}/A_r)/((2r+1)n), STEP holds iff g ≤ 1):
- THIN (prize β 4.0-4.5, n=16,32): g(r) ≤ 1 at EVERY r [STEP holds], AND g(r) DECREASES in r
  (n=32 β=4.5: 0.97,0.94,0.91,0.88,0.85,0.82,0.80) — the step gets EASIER at deeper r in thin (growing
  margin). (A_{r+1}/A_r)/M^2 stays 0.15-0.8 ≪ 1: the consecutive-moment ratio is far below the sup at
  accessible r (heavy tail not yet dominating).
- THICK (maximally-2-structured n=32/F_4129, β=2.40): g(r) = 1.145, 1.225, 1.167, 1.050, … > 1 at low r
  [STEP FAILS], exactly the rungs where A_r > Wick.

NET: the open core reframes to the SINGLE consecutive-moment-ratio bound `A_{r+1}/A_r ≤ (2r+1)n` at r~log q,
which holds thin with MEASURED GROWING margin and fails thick (rule-3-correct). The growing thin margin at
accessible r is encouraging but the deep-r limit A_{r+1}/A_r → M^2 = the prize; NOT a closure (proving the
single step uniformly at r~log q in thin = BGK). Probe scripts/probes/probe_407_moment_ratio_step_thinness.py.
