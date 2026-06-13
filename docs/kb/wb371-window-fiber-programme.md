# The window fiber–pencil programme (#371): the WB residual, brick by brick

> Lane state as of 2026-06-12.  Goal: discharge `WindowRationalBounded`
> (`WBPencilBelowUDR.lean`) — the single named residual of the below-UDR law —
> by structural analysis of the doubly-rational bad-scalar supply, lifting the
> unconditional production floor from `(1−ρ)/3` to the unique-decoding radius
> `(1−ρ)/2`.  Everything here is k = 1 (the current battleground); the
> machinery is k-generic at the identity level.

## The reduction chain (all axiom-clean, in-tree)

1. **WB-2** (`epsMCA_le_max_doublyRational`, pre-existing): below UDR the MCA
   sup is carried by doubly-WB-solvable stacks; far rows cost `(w+2)/q`.
2. **Möbius halving** (`MobiusMCASymmetry.lean`, new): the involution
   `x ↦ −x⁻¹` with twist `x^{k−1}` is a code-stabilizing monomial map; the bad
   set is invariant (`mcaEvent_rs_mobius`, via `mcaEvent_monomial`), `WBSolvable`
   transports (`wbSolvable_mobius`), and `windowRationalBounded_of_halfFamily`
   halves the verification space to Möbius-orbit representatives.
3. **The division identity** (`WindowFiberPencil.lean`,
   `WindowChainStructure.lean`): every bad γ of a reduced-coprime stack yields
   the exact identity `R₀ℓ₁ + γ·R₁ℓ₀ − p·ℓ₀ℓ₁ = g·m_S` with `g ≠ 0` and the
   graded budget `deg g + |S| ≤ 2w` (`witness_division_identity_window` —
   parametric over ALL rows; `deg g ≤ 3w − n` on the window, ladder-reach zero
   above it; the zero-class dies on reducedness + locator coprimality).
4. **γ-elimination** (`witness_cross_dvd`): complement-multiplied cross
   relations give `ℓ₀ ∣ g₂m̂₁ − g₁m̂₂` — the bad family lives in the graded
   solution module of `m̂ ≡ u·g (mod ℓ₀)`, i.e. the **Padé/continued-fraction
   lattice** of the stack class (Berlekamp–Massey structure).
5. **Pencil row** (`stratumG_firstRow_badScalars_card_le`): at `n = 3w` the
   multipliers are constants, the complements form a pencil through `ℓ₀`
   (`SplitPencilBound.lean`: split members of such a pencil are pairwise
   root-disjoint, ≤ `n/w + 1`), and bad ≤ `n/w + 1` — the doubly-rational
   sharpening of the top strip row.
6. **Chain-family kill** (`cored_gamma_unique`): at slack 1 the witnesses
   sharing a `(w−1)`-core have multipliers `a·(X−τ)` with a COMMON scalar
   (`chain_pair_factor`); the identity cancels `(X−τ)` exactly
   (`chain_member_exact`: `Φ·m_K = a·m_D`), distinct cores are impossible, and
   the whole cored family carries **≤ 1 bad scalar**.
7. **Exotic rigidity** (`WindowExoticBound.lean`): per-witness γ-uniqueness for
   polynomial multipliers (`witness_gamma_injective_poly`), and the pair
   dichotomy (`witness_pair_dichotomy`): distinct slack-1 complements share
   ≤ 1 point or a `(w−1)`-core.

**Slack-1 census** (stratum G): bad ≤ 1 (cored family) + #exotics; exotics are
pairwise ≤ 1-intersecting `w`-subsets, so pair-counting caps them at
`C(n,2)/C(w,2)` — within the `w+3` budget for `w ≥ 6`.  Named residual: the
small-`w` exotic sharpening (probe ceiling: 3).

## Strata map (first row; pole rows recurse)

- **G×G reduced coprime**: items 5–7.
- **Shared locator factor** (`gcd(ℓ₀,ℓ₁) ≠ 1`, nonvanishing): zero bad — the
  factor divides the constant `g`.  (Math done; Lean queued.)
- **Codeword row** (`ℓ₀` constant): ≤ 1 bad via translation equivariance.
  (Math done; Lean queued.)
- **Pole rows** (`PoleSpikeMatching.lean`, new): the stratum-agnostic
  `witness_defect_dichotomy`; defect witnesses contain every pole
  (`pole_witness_contains_poles`); misaligned pole pairs pin γ
  (`pole_misaligned_pins_gamma`).  Fully-aligned spikes cancel `m_Z` and
  recurse to a degree-deficient G-instance on the punctured domain — the
  slack-`z₀` rung of the same ladder.

## Probe record (`scripts/probes/probe_wb371_*.py`)

- Faithful `WBSolvable` window caps: bad ≤ w+1 at every tested scale/stratum
  ((13,6,1,2) exhaustive σ-invariant; (13,12,1,4); (11,10,1,4) deep window);
  extremals are Möbius-symmetric with σ-orbit pole alignment.
- Pure incidence is insufficient: MaxCollinear of the page configuration
  reaches w+4 (and 11 via partial-fraction spaces) — the joint clause and
  CRT-realizability are load-bearing.  Core+pairs rank-3 law; f*(12,4) = 3 =
  n/w attained by a μ₁₂ partition (the μ_w-coset pencil is extremal).
- The two-sided witness system (mod ℓ₀ + mod ℓ₁ + leading term) is sound and
  TIGHT on stratum G (0 coverage gaps; count = faithful bad).
- Graded slack-1 fiber = unique-core chain + ≤ 2 exotics; ungraded counts are
  vacuous (59–116) — the budget `deg g ≤ D_def − (w − |T̂|)` is essential.

## The nine-hypothesis disposition (campaign discipline)

The opening dossier ran three reasonable (R), three novel (N), three synthetic
(S) hypotheses.  Status after the first brick campaign:

| # | Hypothesis | Disposition | Artifact |
|---|---|---|---|
| S1 | Möbius involution = MCA monomial symmetry | **PROVEN** | `MobiusMCASymmetry.lean` |
| R1 | Δ-channel split (zero-class vs defect) | **PROVEN** (transformed) | `witness_defect_dichotomy`; per-stratum zero-class kills |
| N2 | Ratio-variety / incidence bound | **SPLIT**: division identity + pencil bound proven; pure-incidence sufficiency REFUTED | `WindowFiberPencil.lean`; `probe_wb371_scale2_incidence.py` (MaxCollinear ≥ w+4) |
| N1 | Möbius renormalization (σ-quotient RG) | OPEN — foundation laid by S1; quotient step unformalized | swarm renormalization probes |
| S2 | Census ↔ window unification | PARTIALLY CONFIRMED — coset pencils = census configurations, strip value `n/(b−1)` = pencil count `n/w`, quartet recursion ↔ fold | this page §1; crystallization open |
| R3 | δ* = census crossing | GATED on the coupling wall (unchanged) | `CensusConditionalPin.lean` |
| S3 | Plancherel two-family law | GATED on the √q kernel | — |
| R2 | Johnson via `CellPackageSupply` | OPEN in-tree residual, untouched by this lane | `Hab25JohnsonPackageSupply.lean` |
| N3 | Isotropy-radius discriminant | DROPPED — no probe support found | — |

Successor generation (spawned by refutations, per discipline):
- **G3-a** (ungraded fiber cap) — REFUTED (`probe_wb371_g3_subspace_split.py`).
- **G3-b** (graded ℓ₀-side cap) — REFUTED (chains survive grading).
- **G3-c** (two-sided count) — probe-CONFIRMED sound + tight; slack-1 instance
  PROVEN (`stratumG_slack1_badScalars_card_le`).
- **CF-telescope** (higher slack) — OPEN, the next rung.

## Open targets, in order

1. Slack-1 assembly (`bad ≤ 1 + exotics` capstone + strata wiring) and the
   small-`w` exotic bound.
2. Pole-recursion bricks (aligned case → punctured deficient instance).
3. Higher slack: the chain theory at `deg g ≤ s` (multi-level CF; the
   `(X−t)`-cancellation telescopes), toward the parametric all-rows theorem.
4. Assembly: `WindowRationalBounded` ⟹ `epsMCA_le_below_udr` unconditional ⟹
   `δ* ≥ (1−ρ)/2` at production shape; strip-row sup-side closure (the KB §5.7
   "lower strip rows" open) via the same machinery.

## The rung census campaign (2026-06-12 session): conjecture refuted, ceiling found

**`bad ≤ 16 = n` is FALSE** at the rung instance (p=12289, n=16, k=3, s=7).
Record progression: pencil 16 → 2-block frame design **20** → fiber-tuned
(6,6,3) ladder **22**. Constructions and exact censuses in
`scripts/probes/probe_wb371_blockframe{,4}.py`, `_hillclimb.py`,
`_blockladder{,2}.py`; issue comments 4691612135, 4691666556.

The three caps that match all probe data exactly:
1. **Per-(maximal A, frame): n − |A|** — PROVEN (`RungMaximalFrame.lean`,
   `maximal_frame_attached_card_le`; maximality closes the h-root escape).
   Tight: pencil = 2 frames × 8 (|A|=8); 2-block = 2 × 10 (|A|=6).
2. **Pencil-root cap**: a witness using > 2 collision points in one big
   block forces the difference pencil to degenerate (deg ≤ 2 members have
   ≤ 2 roots) — the q-collapse seen in the naive ladder.
3. **All-equal-kernel cap**: ns fiber-tuned small scalars impose 4ns linear
   equations on the 18 block coefficients; at ns = 3 only the 6-dim
   all-equal kernel remains ⟹ ns ≤ 2. A 4th glued micro-block collapses
   the census to 9 (gluing rigidity).

Multi-block collapse: 3-block 16, 4-block 1, 5-block 0 (packing: three
disjoint 6-sets need 18 > 16 points; gluing constraints crush the
q-difference space — at 4 blocks it is 1-dim, all cross-ratios constant).

**Empirical ceiling 22 ≤ 31: the obligation `SubCeilingInteriorCeiling ≤ 31`
looks TRUE with margin.** Formal assembly skeleton: 1 (zero-class, proven)
+ Σ big classes (n−|Aᵢ|: per-class proven; ≤ 2 classes by packing)
+ ≤ 2 fiber-tuned extras (kernel-dim argument — TO FORMALIZE)
+ pool ≤ 2 (triple relation `RungTripleRelation.lean` — count TO FINISH).

**Escape-scan addendum** (same session): structured (pairing, γ-triple)
scans found 4420/30516 systems with rank < 12 (escape pairings have visible
μ₁₆ reflection structure, e.g. block-2 pairs (6,11),(7,10),(8,9)), but ALL
escape kernel directions carry `q₁ = q₂` identically — any kernel vector
glues the big blocks and destroys the base 20. ns = 3 stays impossible with
genuinely distinct blocks. **Ceiling 22 verified against: random search,
hill-climb, multi-block, glued micro-blocks, structure-aware escapes.**

## THE REDUCTION (landed): the 5/8 pin = one identity-level Prop

`RungEventInterface.lean` + `RungThresholdRouter.lean` +
`RungInstanceF12289.lean` (all axiom-clean): the interior obligation of the
level-1 rung pin reduces to

  `IdentityCensusBound dom4134 2 7 31` — every stack of deg-<16
  interpolants carries ≤ 31 scalars with a size-≥7 non-joint
  defect-identity witness (deg P ≤ 2),

via `mcaEventNat_iff_defect` (event ⟺ identity), the in-A joint kill
(`rows_explainable_of_witness_in_agreement` — bad witnesses leave agreement
sets; discharges the per-class cap's nonempty-off-part hypothesis), the
census routers through `MCAExactKit`, the threshold band router (one bound
at t₀ = 7 covers all δ < 5/8), and the literal instance wiring
(`orderOf_4134' = 16` via the ℕ-congruence `4134⁸ ≡ −1`). Issue comment
4694739379. Open heart: the class-coexistence count (probe ceiling 22,
margin 9; per-class and pencil-root caps proven, all-equal-kernel cap and
pool ≤ 2 unproven).

## Negative result: bookkeeping-only assembly routes are insufficient

With the class keystone landed (`RungClassPartition.lean`), the gap is
exactly `#solo + Σ_classes (n−|A_j|) ≤ 30`. Two natural counting-only
routes FAIL — recorded so nobody re-walks them:

1. **T-multiplicity (3-subset Fisher with class corrections)**:
   `35·#Γ⁺ ≤ 560 + Σ_K E_K`, `E_K ≤ Σ C(w_i,3) − C(w_max,3)`. Leaks at
   two `a = 8` classes with `w = 8` members (witnesses ⊇ A, size 9):
   bound evaluates to 38 > 31 while the config shape is realizable (it is
   the pencil with enlarged witnesses; truth there is 16). Big witnesses
   make C(w,3) grow at off-cost 1 — the route cannot distinguish
   configuration capacity from algebraic realizability.
2. **Linear exchange (35·#solo + 15·Σc ≤ 560)**: per-member unique-T
   count ≥ C(6,2) = 15 is tight at (w=6, off=1); the LP optimum allows
   Σc = 37 > 30 at #solo = 0 (e.g. three glued size-6 classes), which
   only the GLUING rigidity excludes.

**Conclusion**: the class-coexistence proof must use the algebraic
coupling — the per-class candidate map `γ_K(x) = −(R₀−r_K)(x)/(R₁−q_K)(x)`
(every member's scalar is pinned at EVERY off-point: multi-point off-parts
force ratio constancy), the cross-class collision pencil
`Ψ_{12} = R₀·Δq − R₁·Δr + (r₁q₂−r₂q₁)` (deg ≤ deg R₀R₁ shape, rank-2 in
(R₀,R₁)), and the gluing equation `q₂−q₁ = m_{A₁}h₁ − m_{A₂}h₂` whose
3-class version exhibits the one-level-down recursion (Φᵢ = m_{A_i}h_i
pairwise deg≤2-close ⟹ Φ has the same agreement structure as R₁, one
level down). Empirical margin: ceiling 22 vs budget 31 — crude forms of
these laws suffice.

## Sum-bound shortcuts REFUTED (the residual needs the full coupling)

The `ClassPackingBound` sum bound `Σ(n−aⱼ) + #solo ≤ 30` is NOT closable by
any single counting lemma on the agreement sets or factor products in
isolation. Two natural shortcuts both fail (probe `probe_wb371_esym.py` +
the earlier bookkeeping note):

1. **Fisher on agreement sets** (pairwise share ≤ 2): allows ~28 size-6
   sets → contribution ~280.
2. **e-symmetric confinement** (`D = a`, `h` constant ⟹ `m_{Aⱼ}` share top
   `a−3` elementary symmetric functions): `probe_wb371_esym` finds up to
   **6** size-6 subsets of μ₁₆ sharing `(e₁,e₂,e₃)` (the 4 maximal profiles
   × 6 — a coset/orbit structure), contribution 6·10 = **60 > 30**. Counts
   by size: a=5→12, a=6→6, a=7→1, a=8→2.

Moreover the **record-22 extremal does not satisfy the `D=a` premise**: its
two big agreement blocks A₁={0..5}, A₂={6..11} have DIFFERENT top-3
symmetric functions `(2571,9386,3562) ≠ (4887,2903,1542)`, so there `h` is
non-constant (`D > a`) — the confinement lives on the full product
`Φ = m_A·h`, not `m_A`.

**Conclusion**: the sum bound requires the FULL gluing coupling acting on
all classes simultaneously (factor confinement + agreement Fisher + frame
pinning + the degree collapse + off-part disjointness), not a reduction to
one of them. This is why `ClassPackingBound` is the right named-residual
endpoint: it is genuinely as hard as the rung at this instance, with every
surrounding law proven. Empirical truth 22 ≤ 31 (margin 9), but no clean
counting certificate is known — the residual is real.

## The sum bound is an ATTACHMENT-gated count, not R₁-graph incidence

Reframing (`probe_wb371_incidence.py`): since `Φ_j = m_{A_j}h_j = R₁ − q_j`
definitionally, a frame class is exactly a quadratic `q` (deg `< k`) whose
agreement set `A_q = {i : R₁(xᵢ) = q(xᵢ)}` (points of R₁'s graph on the
curve `y = q(x)`) hosts `≥ 2` attached bad scalars; `cap = 16 − |A_q|`.

Measured:
* **record-22 R₁**: exactly **2** quadratics with `a_q = 6` (the two big
  classes), 520 with `a_q = 3`; UNGATED `Σ_{a_q≥2}(16 − a_q) = 6780`.
* **random R₁**: ALL 560 quadratics have `a_q = 3` exactly (no clustering).

So R₁-graph incidence is generically trivial (every triple spans its own
quadratic, none richer), and the ungated sum is ~6780. The
`≥2-attached-bad-scalars` GATE must cut this by a factor of >200 to reach
`≤ 30`. **The entire content of the sum bound lives in the attachment gate
— the R₀-frame coupling (a quadratic hosts a bad scalar only when R₀'s
frame `r` and a non-joint size-≥7 witness exist) — NOT in the agreement
geometry of R₁ alone.** This redirects the attack: the `RungOffPointPinning`
/ `RungCrossRestriction` frame laws (R₀-side) are the operative constraint,
not the Fisher/e-symmetric counts (R₁-side, both already refuted as
shortcuts). The named residual `ClassPackingBound` correctly bundles this:
its hardness is the R₀-R₁ joint frame-attachment count.

## Correction: the n−|A| per-class cap is LOOSE; the bound is the shared-R₀ coupling

A subtlety in the `ClassPackingBound` framing, found while testing 3-class
coexistence: three DISJOINT size-5 agreement sets (15 pts) coexist
geometrically (R₁ = qᵢ on Aᵢ is consistent at deg ≤ 15), so
`Σ(n − |Aⱼ|) = 3·11 = 33 > 31`. Hence the partition bound with caps
`n − |A|` (`maximal_frame_attached_card_le`) does NOT by itself give ≤ 31 —
the cap is loose. The obligation must hold because each class hosts FEW
ACTUAL attached scalars, not because few classes coexist.

The operative mechanism (the shared single R₀): a class-`i` bad scalar with
witness `Aᵢ ∪ T` (`|T| = 2` off-`Aᵢ`) needs `T` to lie on the candidate
map `fᵢ = −(R₀−rᵢ)/(R₁−qᵢ)` at one shared value. But the off-points of
class `i` are LARGELY the agreement points of classes `j ≠ i`, where R₀ is
PINNED to `rⱼ` (their frame). So `fᵢ` on `Aⱼ` is determined by the other
classes' frames — not freely maximizable. This is exactly the regime of the
landed `cross_restriction_card_le` (`RungCrossRestriction`): a fixed scalar
is served by ≤ `k−1 = 2` frame points of another class. The only truly free
off-points are the few outside every `Aⱼ` (here 1), too few to form witness
pairs.

**Corrected residual focus**: the per-class attachment count is bounded by
`fᵢ`-value collisions among the (mostly R₀-pinned) off-points, governed by
`cross_restriction` — NOT by `n − |A|`. The right `ClassPackingBound` cap is
the cross-restriction collision count, and the global bound is the
shared-R₀ coupling across all classes. (The `probe_wb371_sharedR0` hill-climb
was inconclusive — single-coordinate moves cannot bootstrap a bad scalar
from a random stack; a constructive multi-class builder is needed to push
the empirical max past the fiber-tuned 22.)
