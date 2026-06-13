# Two √-boundaries, same objects, different walls — a deflation note (do NOT re-chase as a unification)

2026-06-13. Recorded so the resemblance is not mistaken for a theorem by a later pass.

Two square-root boundaries appeared independently this week:

- **Ceiling lane (swarm):** the sharp-band law `r² < 2^μ` (`KKH26DimGeneralSharpPin.lean`,
  commit `0a741dfe1`; reach corrected to `r < √n` in `8081d3b7b`). Counts KKH26 bad
  scalars = antipodal-free signed `r`-subsets of the order-`2^μ` subgroup.
- **Census lane (mine):** the conjectured activation law `N_r(s) > 0 ⟺ r² ≤ s+1`
  (`exclusion/REPORT.md`), with the proven skeleton T1/T3 + 29 certificates.

A build→adversarial-analysis pass (the verify leg did not complete — session limit — so
this is **analysis-grade, not audited**) found:

**Verdict: RELATED-BUT-DISTINCT. No theorem transfers in either direction.** The
resemblance is real at the *object* layer and cosmetic at the *theorem* layer.

- **Object identity (real):** with `2^μ = s` (NOT `n = 2s`), the swarm's bad-scalar index
  family is literally my pure `(O,m)` sign-class space — both have count `2^r·C(s/2, r)`
  (checked: `1792 = 2⁵C(8,5)`, `1024 = 2⁷C(8,7)`, `139,776 = 2⁷C(16,5)`, …), and the
  swarm's bad scalar `λ_T = −Σ_{x∈T} x = −e₁(T)` is exactly my L4 quantity `ξ = −Σxᵢ`.
  The shared bedrock is the in-tree 2-power Lam–Leung antipodal decomposition (their
  bricks; my RESULTS §6 already records my own copy as redundant).
- **Different quantities (the deflation):** the ceiling law bounds a *cardinality ratio*
  (ownership) for a degree-`r−2` low-rate code; my law is *existence* of an antipodally
  balanced `e₂`-multiset for the rate-½ descent code. No parameter choice equates the
  codes (`r ≤ 2^{μ−1}` deg `r−2` vs my deg `s−1`).
- **The walls diverge at matched parameters:** the ceiling's *true* band wall grows like
  `√(n ln n)` (exact walls 6, 10, 16, 26, 40, 61 at μ=4..9); my sharp wall is `√s`.
  Domain-matched counterexamples to any "same boundary" claim: `(μ=5, r=5)` band nonempty
  yet `N₅(16) = 0` proven; `(μ=6, r=7)` band nonempty yet `N₇(32) = 0` proven (full
  215,414,784-config sweep).
- **The ±1 coincidence (why they look identical on the lattice):** in budget coordinates
  (`b = (s+1−r)/2`), the ceiling's strict `r² < 2^μ ⟺ C(r,2) ≤ b−1`, my `r² ≤ s+1 ⟺
  C(r,2) ≤ b`. These agree at every (2-power `s`, odd `r`) lattice point **except** the
  unique solution of `(r−1)(r+1) = 2^j`, namely `(s,r) = (8,3)` — my boundary-tight
  `N₃(8) = 8`. A perfect ±1 offset between a *proven-sufficient* condition for one
  quantity and a *conjectured-sharp* condition for another.

**Why this is NOT paperworthy as a transfer:** the ceiling's proven band-nonemptiness
proves no cell of my conjectured law (it asserts subset-sum family sizes, not balanced-config
existence, and stays nonempty where my strata are proven empty); my T1/certificates settle
nothing the ceiling lane lists as open (its `√(n ln n)` general theorem is pure binomial
analysis). **The only genuine unification already happened at the foundation** (both lanes
run on the same in-tree Lam–Leung bricks).

**Actionable takeaway:** neither lane should cite the other's √-boundary as evidence for
its own — the constants differ (`√(n ln n)` vs `√s`). That cross-reference is the entire
value of the observation.
