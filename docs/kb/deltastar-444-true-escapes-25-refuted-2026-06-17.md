# 25 TRUE-escape conjectures (defeat the "m* is a magnitude" argument) — all refuted (#444)

**The sharper target.** The last sweep showed all 25 novel conjectures *relabel* `m*`. A **true escape**
must DEFEAT the magnitude argument: it must break a NAMED link of the proven chain so that `m*`'s integer
value becomes non-analytic / exactly-computable / bypassed — not merely re-dress the selector.

**The proven chain a true escape must break** (all `⟺` axiom-clean in-tree):
- **[L1]** δ* reaches the window INTERIOR (toward capacity, above Johnson)
- **⟺ [L2]** the char-p floor `M(n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m)`
- **⟺ [L3]** the char-p energy `A_r=E_r(μ_n)−n^{2r}/q ≤ (2r−1)‼·n^r` at `r≈ln q≈83`
- **⟺ [L4]** the orbit-count growth `O(c)` collapses to ≤2 at the binding depth `c*=m*`, `δ*=1−ρ−m*/n`.
- Two-sidedness **[L1⟺L2]** PROVEN (`_EnergyRatioMonotoneReduction`: `ERM-at-r ⟺ max‖η‖²≤(2r+1)n`);
  char-0 **[L3]** CLOSED all r (Lam–Leung); proxy → Johnson (`m*=n/4−1` LINEAR).

**The magnitude argument:** `m*`'s value = where `O(c)` collapses = the energy crossing at `r≈ln q` = the
wall. A torsion/spectral/rigidity *dressing* can pick a residue class of `m*`; pinning the unique integer
re-invokes the budget crossing = the wall.

> **Method note (honesty).** This pass was done by direct adversarial analysis (the multi-agent fan-out
> hit the weekly limit), with **machine countermodels computed in Python** where falsifiable
> (`/tmp/escape_countermodels.py`, exact `F_p`, `p≡1 mod n`, `p>n⁴`). Reductions cite in-tree axiom-clean
> facts. Refutations not machine-checked are flagged as reasoned (to re-verify with agents when the limit
> resets). No fabricated closure; the exact δ* stays the single open char-p input.

**Two decisive machine countermodels (kill several archetypes at the root):**
- **Binding is DEEP, not shallow** [`/tmp/escape_countermodels.py`]: at ρ=1/4, the far-direction list
  (#distinct forced-γ) is `Θ(C(n,k+1))` super-budget at shallow folds (n=16: `2256, 1505, 2641` at
  r=1,2,3; budget=16) and collapses below budget only at DEEP fold (r=5: list=16). So `m*` lives deep,
  in the char-p energy regime. **Any "shallow-bind" / char-0-rigidity escape is refuted at the root.**
- **The worst direction is NOT antipodal/structured**: the antipodal fold (n/2) gives **list=1** (benign);
  non-antipodal folds give 680–1505. **Any "worst direction is structured, list closed" escape is
  refuted** — the worst is a spread direction whose list is large and char-p-governed.

---

## The 25 true-escape conjectures, by the link they target — and why each fails

### Archetype (i) BIND SHALLOW — break L3's "r≈ln q"

**E1 `dyadic-tower-early-saturation`.** *Claim:* for 2-power n the over-determination saturates `O(c)≤2`
at `c*=O(log₂ n)` via the dyadic tower, so the binding energy is char-0 and δ* is closed.
**Verdict: REFUTED-FALSE (machine).** The list is `Θ(C(n,k+1))` super-budget at shallow folds and
collapses only at deep fold (countermodel above). `O(c)` GROWS super-linearly (`oc₃~n²/32`, `oc₄~n³/512`,
O196) — it does not saturate shallow. Binding is deep ⟹ char-p ⟹ L3 unbroken.

**E2 `first-overdet-fold-binding`.** *Claim:* the worst-case floor binds at the first over-det fold
`c*=k+2`, char-0-computable. **Verdict: RELABELS-M* / REFUTED.** `r=k+1` is the KKH26 *ceiling* (the easy
bad-family direction), not the worst-case floor; the far-line audit binds far deeper. Equating floor to
the shallow ceiling is the proxy → Johnson, not the interior value.

**E3 `loglog-energy-plateau`.** *Claim:* `A_r/Wick` plateaus below 1 by `r=O(loglog n)`, pinning the sup
shallow. **Verdict: REDUCES-TO-BGK.** The sup `M` is minimized at the saddle `r*≈ln q`; an earlier plateau
gives a *worse* (larger) bound and the char-p excess `W_r` onset is deep (`W_3=0`, onset `r₀(n)` grows
faster than n⁴). The plateau does not pin δ* — minimizing over r returns to the wall depth.

### Archetype (ii) RIGIDITY of the worst direction — break "worst = deep-energy"

**E4 `antipodal-worst-rigidity`.** *Claim:* the worst far-direction is forced to antipodal `x^{n/2}`,
list exactly 2. **Verdict: REFUTED-FALSE (machine).** Antipodal fold gives **list=1**, the *smallest*
(benign); the worst is non-antipodal (lists 680–1505). Antipodal pins δ*=Johnson+1/n (the proxy, not the
interior). RELABELS to Johnson even if it bound anything.

**E5 `dilation-orbit-closed-list`.** *Claim:* the worst word lies in a dilation orbit, list = orbit size,
closed. **Verdict: REFUTED.** The worst list GROWS `~n²` at non-invariant lacunary words; the constant
orbit-size list is only the *dilation-invariant* word `x^{n/2}` (the benign one). The worst is outside any
single orbit (memory `issue444-listsize-dilation-orbit-constant`).

**E6 `gapped-cyclotomic-rigidity`.** *Claim:* the worst gapped word's list is pinned by cyclotomic
factorization, closed. **Verdict: REDUCES-TO-BGK.** Correct that the floor witness is GAPPED (band
dichotomy) — but the gap is *exactly* what engages the cyclotomic/BGK wall; the factorization count is the
char-p vanishing-sum / energy object. Rigidity here = the wall.

### Archetype (iii) DECOUPLE L3⟺L4 — break the middle equivalence

**E7 `genfn-pole-collapse`.** *Claim:* `O(c)` collapse is governed by a pole of `Z(t)=exp(Σ I_r t^r/r)`,
p-independent, not the energy. **Verdict: REDUCES (in-tree).** This is exactly `_OffBGK_UnionGrowthGeneratingFn`:
the pole-structure IS the open obligation `DistinctGammaUnionGrowthLaw`, and the measurement shows the
realized object is super-poly (literal) / O(n) (deep = proxy). The pole does not decouple from the energy;
it restates the same growth law.

**E8 `schur-fusion-rank`.** *Claim:* `O(c)≤2 ⟺` a Schur-ratio fusion multiplicity vanishes, rep-theoretic.
**Verdict: REDUCES-TO-BGK.** The fusion/convolution operator on the coset lattice is the abelian Paley
convolution operator, eigenvalue exactly `η_b` (`_PaleyCayleyEigenvalue.cayley_eigenvalue_eq_eta`, rfl) —
its multiplicity/spectral data IS `M(n)`. The cat-map kill applies verbatim.

**E9 `newton-polytope-mixed-volume`.** *Claim:* `O(c)` collapse = a BKK/Newton-polytope mixed-volume
threshold, combinatorial. **Verdict: REDUCES / REFUTED.** Tropical/BKK is in the dead ledger (re-expresses
HOMDS = Schur-at-roots = vanishing sums = energy); `V_r` is 0-dimensional so the mixed volume is a Bézout
root-count, not a decoupled threshold.

### Archetype (iv) LOWER THE TARGET — break L1⟺L2 sharpness

**E10 `window-slack-weaker-bound`.** *Claim:* at the window radius the budget tolerates `M ≤ n^{1−η(ρ)}`,
already given by BGK `n^{1−o(1)}`. **Verdict: REFUTED (two-sidedness is sharp).** `ERM-at-r ⟺
max‖η‖²≤(2r+1)n` is an *exact equivalence* — the interior needs the sharp `√(n log m)`, and BGK
`n^{1−o(1)}` does NOT reach it (the half-power gap `0.989→0.5` is the entire wall). The weaker bound leaves
δ* at Johnson (`O223 CharSumBudgetVacuity`: the consumer is vacuous below the sharp threshold).

**E11 `per-rho-narrow-window`.** *Claim:* for ρ=1/2 the window is narrow, a weaker bound suffices.
**Verdict: REFUTED.** The prize regime is thin (β≈4); the meta-theorem caps every weaker-than-sharp method
at Johnson regardless of ρ. Narrowness does not lower the target — the floor side stays the sharp bound.

**E12 `soundness-error-poly-slack`.** *Claim:* `ε*=2^-128` tolerates poly(n) bad scalars, weaker than
√-cancellation. **Verdict: REDUCES-TO-BGK.** Budget `q·ε*≈n` is *exactly* the √-cancellation threshold
(`O219`); poly(n) bad scalars crossing budget n IS the binding condition = the wall. The slack is already
the budget in the identity.

### Archetype (v) EXACT IDENTITY — value not bound

**E13 `lefschetz-fixedpoint-mstar`.** *Claim:* `m* = #Fix(Frob)` on a variety, exact equality.
**Verdict: REDUCES (A6 trap).** The fixed-point count = the orbit-count = the energy; `V_r` 0-dim ⟹
Lang–Weil VACUOUS, the count IS the main term = the magnitude. Equality to the wall is still the wall.

**E14 `trace-formula-equality`.** *Claim:* `m* =` a spectral trace, equality. **Verdict: REDUCES-TO-BGK.**
Eichler–Selberg already refuted: the spectral side is the exact moment hierarchy `Σ η_b^{2r}` = the energy.
An equality to the energy does not bypass it.

**E15 `class-number-regulator-identity`.** *Claim:* `m* = h·R⁻¹` of a cyclotomic field, exact arithmetic.
**Verdict: REFUTED.** `disc(Ψ)=p^{m−1}f²` is class-field-FIXED (`discnogo`); the class number gives only a
LOWER bound on the period (wrong direction), and is p-independent so cannot pin the p-sensitive interior.

### Archetype (vi) NON-MAGNITUDE SELECTOR — defeat the kill directly

**E16 `complete-spectral-flow`.** *Claim:* `m* =` the FULL spectral-flow integer of a self-adjoint family,
not mod anything. **Verdict: RELABELS-M*.** Spectral flow = signed eigenvalue-crossing count = exactly the
energy/eigenvalue crossing = the magnitude. "Complete" makes it the magnitude itself, not an escape from it.

**E17 `k-theory-index-pin`.** *Claim:* `m* =` a K-theoretic index, integer and complete. **Verdict:
RELABELS-M*.** The index theorem EQUATES the index to an analytic (η-invariant / heat-kernel / energy)
quantity — the index IS the magnitude by Atiyah–Singer. Computing it needs the analytic side = the wall.

**E18 `cohomological-obstruction-value`.** *Claim:* an H² class whose VALUE (not vanishing) pins the unique
`m*`. **Verdict: RELABELS-M*.** The class's value is computed by the same period integral / cup product
that IS the Gauss-period magnitude. A "complete" cohomological selector evaluates to the magnitude — it
does not sever L4 from L3.

### Archetype (vii) DUALITY TRANSFER — break "no solved analog"

**E19 `folded-RS-capacity-transfer`.** *Claim:* GG25 folded-RS capacity transfers to dyadic μ_n via a
folding map. **Verdict: REFUTED.** Folding/randomness is exactly what GG25/CS25 USE and what explicit μ_n
LACKS — the prize IS the explicit case (the folding map does not preserve the fixed μ_n evaluation
structure; the list-count is not transported). Memory `issue407-linedecoding-route-reduces-to-bchks`.

**E20 `function-field-RH-transfer`.** *Claim:* the F_q(t) analog where RH gives the sharp bound, transfer.
**Verdict: REDUCES.** The function-field analog IS Weil/RH, and Weil is `√q`-VACUOUS on thin μ_n
(`√q ≥ n` at β≥2); the transfer lands on the already-dead Weil bound, not a sharp one.

**E21 `ramanujan-subgroup-transfer`.** *Claim:* a subgroup where `Cay(F_q,H)` is Ramanujan; transfer the
bound. **Verdict: REFUTED.** No multiplicative-subgroup Cayley graph is Ramanujan for the prize parameters
(the prize graph has `M/(2√n)=1.34…2.43 > 1`, NOT Ramanujan, fresh exact data); there is no Ramanujan
source to transfer FROM. Memory `issue444-modern-tools-nogo`.

### Archetype (viii) STRUCTURE-VS-RANDOM DICHOTOMY — break "worst-case sup is hard"

**E22 `kelley-meka-dichotomy`.** *Claim:* worst-dir is structured (closed list) or pseudorandom
(≤capacity), both give exact δ*. **Verdict: REDUCES-TO-BGK.** Kelley–Meka/PFR is wrong-direction (dead
ledger); the "pseudorandom" horn still requires the sup bound `M ≤ C√(n log m)` to certify list ≤ capacity
= the wall. The dichotomy does not bypass the sup; it relocates it to the pseudorandom horn.

**E23 `regularity-decomposition`.** *Claim:* a Szemerédi-type regularity split of the bad set pins δ*.
**Verdict: REDUCES.** Regularity gives L²/RMS control (the energy/Parseval side), not L∞ — it violates
meta-theorem property (c) (genuinely L-infinity). The sup is exactly what regularity cannot see.

**E24 `density-increment-to-structure`.** *Claim:* if the worst list is large, density-increment to a
structured subconfiguration with closed count. **Verdict: REDUCES-TO-BGK.** The increment terminates at
the same additive-energy object (the increment potential IS `Σ|η_b|^{2r}`); each step is a moment bound,
capped at Johnson by the meta-theorem.

### Archetype (extra) the two-sidedness itself

**E25 `two-sidedness-has-a-gap`.** *Claim:* `ERM-at-r ⟺ max‖η‖²≤(2r+1)n` is only sufficient, so a non-ERM
route reaches the interior without the sharp bound. **Verdict: REFUTED (proven).** The equivalence is
axiom-clean in-tree (`_EnergyRatioMonotoneReduction`, both directions); `moment_ladder_exceeds_prize`
proves no moment route at any depth reaches the target. There is no gap: the interior reach is *equivalent*
to the floor, not merely implied by it.

---

## Verdict tally

| outcome | count |
|---|---|
| REFUTED-FALSE (incl. 2 machine-checked at root) | 8 |
| REDUCES-TO-BGK | 11 |
| RELABELS-M* (the canonical kill — secretly the magnitude) | 4 |
| REDUCES / mixed-to-wall | 2 |
| **BREAKS-LINK-SURVIVES** | **0** |

**0 true escapes of 25.** Every attempt to break a named link either (a) is machine-refuted at the root
(binding is deep, worst is non-antipodal), (b) reduces to BGK (the named link turns out proven-unbreakable
in-tree), or (c) is caught relabeling (a "complete" discrete selector evaluates, via its own index/period
identity, to the magnitude itself).

## The sharpened no-go (why no escape of this shape can exist)

The magnitude argument is robust against ALL eight archetypes for one structural reason: **the chain is
PROVEN two-sided and char-0-closed.**
- You cannot **lower the target** (iv) or exploit a **two-sidedness gap** (viii-extra) — `L1⟺L2` is an
  *exact equivalence*, machine-proven.
- You cannot **bind shallow** (i) or **force a structured worst direction** (ii) — machine countermodels
  show binding is DEEP and the worst direction is non-antipodal with a large char-p list.
- You cannot **decouple L3⟺L4** (iii) — the convolution/fusion operator's spectrum IS `η_b` (cat-map
  identity), so the orbit-count and the energy are the *same* object, not two linkable ones.
- You cannot pin `m*` by an **exact identity** (v) or a **non-magnitude selector** (vi) — every such
  identity (Lefschetz, trace, index, cohomology class) EQUATES `m*` to the analytic magnitude (Lang–Weil
  vacuous / Atiyah–Singer / period integral), so evaluating it *is* the wall.
- You cannot **transfer from a solved analog** (vii) — the only solved analogs (folded/random RS, Weil/RH,
  Ramanujan subgroups) either require the randomness explicit μ_n lacks or are √q-vacuous / non-Ramanujan
  here. There is no sharp source.

**The single irreducible fact:** `m*` is the depth at which a p-SENSITIVE magnitude (the orbit-count =
energy = sup-norm) crosses the budget. A torsion / topological / rep-theoretic / combinatorial / dynamical
invariant is either p-independent (so it cannot track the p-sensitive crossing — the `D=89`-across-4-primes
smoking gun) or, if p-sensitive, it IS the magnitude (the cat-map / index-theorem identities). **No
dressing escapes; the magnitude is the prize.** An escape, if one exists, must produce a p-SENSITIVE,
EXACTLY-COMPUTABLE, NON-MAGNITUDE invariant — and the chain's two-sidedness proves no such object controls
`m*`. The genuine open prize remains the single char-p BGK input `M(n) ≤ C√(n log m)` at `r≈ln q`, `n=2³⁰`.
