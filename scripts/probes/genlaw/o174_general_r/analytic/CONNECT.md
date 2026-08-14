# CONNECT — general-r deep-band #bad-scalar as (e1,e2)-joint level-set vs the moment-subset-sum literature

Worktree: /home/nubs/Git/ArkLib-232 (synced 2026-06-13). Demand-side lane, #389 / ExcessCensusLaw analytic core.
Author seat: Connect. Tags: [PROVEN]/[COMPUTED]/[LIT]/[OPEN]. Anti-fabrication: the object below is OPEN; the
literature does NOT close it. This file states the object exactly, what each paper actually bounds, and the gap.

================================================================================
## 1. THE OBJECT, EXACTLY (the (e1,e2)-joint level-set / 2nd-moment subset-sum count over mu_n)
================================================================================

### 1.1 Parametrization (pinned against in-tree + O172)

- Ground set: `G = mu_n`, the smooth multiplicative subgroup of order `n = 2^k` in `F = F_q`
  (exists only when `2^k | q-1`, so `q` odd, `char F != 2` — this is the regime the in-tree
  `twoSymmetric_fiber_eq_e1_psum2_fiber` `h2 : (2:F) != 0` hypothesis lives in; automatic here).
- High-freq character line: the order-`r` character line `Q0 + gamma * x^{k_c}` at the top
  frequency (`x^{k_c}` = the high-freq monomial direction). Deep band = deficit `a0 - k_c = 2`,
  i.e. the agreement size `a0 = k_c + 1 = r + 1` and the TOP TWO coefficients of the pencil
  polynomial `p_S` must both vanish (deficit 2 ⟹ two degree-drop constraints).
- Subset size: `a = k_c + 1 = r + 1`. (CALIBRATED: r=3 ⟹ 4-subsets; r=8 ⟹ 9-subsets.
  See `r3` closed form below and the n=16 measured ladder.)
- Vieta pin [PROVEN, `DeepBandR3Bound.badscalar_eq_neg_subset_sum`,
  `SinglePencilSharper.witness_pin_eq_neg_sum`]: for an `(r+1)`-subset `S` on the line,
  `gamma = - sum_{x in S} x = - e1(S)`. So the bad scalar is determined by `e1(S)`.

### 1.2 The two constraints (deficit-2 ⟹ e1 AND e2 jointly prescribed)

Both top coeffs of `p_S` vanishing ⟺ [PROVEN, Round 5 `degDrop_t2_iff_two_symmetric`,
recoordinated Round 6 `degDrop_t2_iff_e1_psum2`]:

    e1(S) = sum_{x in S} x        = -g_{k+1}/c        =: c1
    e2(S) = sum_{T in C(S,2)} prod = g_k/c             =: c2

and via Newton `e1^2 = p2 + 2 e2` (in-tree `sq_window_sum_eq`, char-free; cancel 2 needs `2!=0`):

    e2(S) = c2   ⟺   p2(S) := sum_{x in S} x^2 = c1^2 - 2 c2      ([PROVEN] re-coordinatization
    `twoSymmetric_fiber_eq_e1_psum2_fiber`, `twoSymmetric_count_eq_e1_psum2_count`).

So the deep-band joint fiber is the **(sum, sum-of-squares) joint level-set** over `mu_n`:

    N2(c1, c2) := #{ S ⊆ mu_n : |S| = r+1, sum_{x in S} x = c1 AND sum_{x in S} x^2 = c2 }
              (in-tree `Round7SecondMoment.N2`; `c2 := c1^2 - 2*e2target`).

### 1.3 The deep-band #bad-scalar count is NOT N2 itself — it is the e1-axis SUPPORT

CRITICAL distinction (this is where O174's "axis-support mismatch" bites and why a closed-form
per-line route fails for r >= 4). The bad scalars are `gamma = -e1(S) = -c1`. The line FIXES the
ratio `c2/...` structure but the actual count of DISTINCT bad gamma is:

    #bad(r) = #{ distinct c1 in F : exists (r+1)-subset S ⊆ mu_n with e1(S)=c1 AND e2(S)=
                                     (the value the line forces, a function of c1) }

i.e. the deep-band #bad-scalar = the **e1-axis projection (support along the e1 coordinate)** of
the (e1,e2) JOINT level-set, where the e2-target co-moves with e1 along the line. Equivalently, it
is a 1-parameter SLICE of the 2-D support `N2_support` of `N2` (in-tree
`Round7SecondMoment.N2_support`), cut by the line's `e2 = phi(e1)` relation, projected to e1.

This is the exact object O174 isolated. The per-line closed-form route (which worked at r=3 via the
parity-split → antipodal-pair-product collinearity reduction, giving `#bad = n*C(n/4,2)+1`) fails for
r >= 4 because the worst-case monomial family's axis support (which divisor `x^{n/2}` vs `x^{n/4}`
dominates) changes with r: the `x^{n/2}` line that controls r=3 DEGENERATES to `#bad=1` at r=4,
where the `x^{n/4}` family takes over — there is no single per-line algebraic identity whose axis
support tracks all r. [O172 honest scope, RESULTS-Q-THRESHOLD.md.]

### 1.4 The second-moment / collision-count handle [PROVEN, in-tree, axiom-clean]

The natural rigorous control on the joint level-set is its 2nd moment over the target plane:

    sum_{(c1,c2) in F x F} N2(c1,c2)        = C(n, r+1)                 (N2_total)
    sum_{(c1,c2) in F x F} N2(c1,c2)^2      = collisionCount(mu_n, r+1) (N2_secondMoment_eq_collisionCount)
      where collisionCount = #{ (S,S') of (r+1)-subsets : e1=e1' AND p2=p2' }   (the 2-D diagonal)
    Cauchy-Schwarz: C(n,r+1)^2 <= #support * collisionCount       (choose_sq_le_support_mul_collisionCount)
    Sandwich:       C(n,r+1) <= collisionCount <= C(n,r+1)^2      (both endpoints proven)

So `#bad <= #support(N2) <= K` would follow from an UPPER bound on `collisionCount` AND a separation
of the e1-axis slice, OR directly from a per-(c1,c2) UPPER bound `N2(c1,c2) <= small` plus a support
bound. The budget `K = 2^r C(n/2, r)`. The PROVEN trivial bounds leave `collisionCount` anywhere in
`[C(n,r+1), C(n,r+1)^2]`; the prize-deciding magnitude is OPEN.

### 1.5 Calibration (COMPUTED, this seat, matches O171/O172 exactly)

r=3 closed form `#bad = n*C(n/4,2)+1` vs `K = 2^3 C(n/2,3)`:
  n=16: 97/448 (4.62x); n=32: 897/4480 (4.99x); n=64: 7681/39680 (5.17x); → 5.33x as n→∞.  [matches O172]
n=16 measured ladder `#bad` r=3..8 = 97,145,89,113,225,104 vs K=448,1120,1792,1792,1024,256
  ⟹ K/#bad = 4.62, 7.72, 20.1, 15.9, 4.55, 2.46x.  NON-MONOTONE, divisor-dependent.  [matches task]
Worst observed margin: 2.46x (r=8=n/2, the central band, subset size 9). All <= K. [COMPUTED]

================================================================================
## 2. WHAT EACH PAPER ACTUALLY BOUNDS
================================================================================

### [LIT] LMRW — Lai–Marino–Robinson–Wan, "Moment subset sums over finite fields", arXiv:1910.05894, FFA 62 (2020).
WHAT IT BOUNDS:
- Object: `N_k(D,b,m) = #{S ⊆ D : |S|=k, sum_{y in S} y^j = b_j for 1<=j<=m, p∤j}` — the JOINT m-moment
  count. THIS IS OUR OBJECT'S SHAPE (m=2 ⟹ (e1-via-p1, p2) joint count = our N2).
- GROUND SET D: `D = g(F_q)` = the IMAGE of a polynomial `g` (monomials `{x^n}`, Dickson `{D_n(x,a)}`).
  **NOT a multiplicative subgroup.** D has size ~q/deg(g); it is a polynomial image, not a subgroup.
- Main quantitative estimate (Thm 9, "medium k"): `|M_k(D,b,m) - |D|^k / q^{m_p}| < (mn+1)^k q^{k/2}`,
  where `M_k = k! N_k`, `n = deg g`. Error beats main term only when `(mn+1)^k q^{k/2} < |D|^k/q^{m_p}`.
- NON-VACUITY CONDITIONS: `2n(mn+1) < q^{1/6}` AND `3 m_p + 1 < k < q^{5/12}`. The decision algorithm
  (Thm 1) is poly-time but the COUNTING estimate needs these windows.
- Char-sum input (Lemma 1, the partial Gauss sum): `|sum_{x in D} psi(f(x))| <= (mn+1) q` for `D=Dickson`;
  Cor 1 gives the quadratic-character `(mn±1) sqrt(q)`-shape. THIS is the "subgroup_quadratic_sum_is_partial"
  the in-tree note hoped for — but it is over `D=g(F_q)`, not over `mu_n`.

### [LIT] GPP — Gottig–Pérez–Privitelli, arXiv:2401.06964 (2024), diagonal-equation route.
WHAT IT BOUNDS:
- Object: `N_m(k,b,D) = #{S ⊆ D : |S|=k, sum_{a in S} a^i = b_i, 1<=i<=m}` — same JOINT count.
- Thm 1.2 (main, p∤k): `|N_m(k,b) - C(q,k)/q^m| <= M·(-1)^k·C(-sqrt q, k)`, i.e. error ~ `(sqrt q + k)^k/k!`
  ≈ `C(q,k)·q^{-k/2}` (improved exponent `O(p^{sk/2})` from prior `O(p^{(s-1)k})`).
- GROUND SET D: **`D = F_q` (the FULL FIELD)**; Section 5 extends to `D = {f(x):x in F_q}` polynomial
  images. **NOT a multiplicative subgroup.** The method "exploits complete-intersection geometry and
  does NOT require multiplicative structure on D" (their words) — it needs D to be all of F_q or a poly image.
- NON-VACUITY (Thm 1.4): `D=F_q`, `m <= (k-25)/50`, `k <= q^{0.24}` ⟹ `N_m(k,b) > 0` for ALL b. Linear
  `m=O(k)`. Conditions for the asymptotic: `q > 2^21`, `p>=5`, `k <= 2q^{0.9}-sqrt q+1`, `m <= k/20`.
- t=2 specifically: covered as the `m=2` case of the general theorem; NO subgroup-specific t=2 result.

### [LIT] CDK — Christie–Dykema–Klep, "Classifying minimal vanishing sums of roots of unity", arXiv:2008.11268.
WHAT IT BOUNDS:
- Classifies MINIMAL vanishing sums of n-th roots of unity up to WEIGHT 21 (extends Poonen–Rubinstein wt 12).
- For `n = 2^k` (dyadic): minimal vanishing relations are highly 2-adically constrained; the Lam–Leung
  weight set for `n=2^a` is `W(2^a) = {2,4,6,...}` (the even numbers, generated by the single prime 2) —
  i.e. EVERY minimal vanishing 2-power relation is built from antipodal pairs `{z,-z}` (weight-2 atoms),
  though at higher weight non-pure cancellations appear. NO general bound on the NUMBER of minimal sums
  of given weight is given.
- ROLE for us: governs WHICH deep-band bad configs EXIST (a vanishing relation among the line values is
  what makes a config "bad"); the dyadic weight-2-atom structure underlies the r=3 antipodal pair-product
  reduction. It does NOT count #bad — it characterizes the support of the relation lattice, not the level-set.

### [LIT] Łaba–Marshall, arXiv:2202.07555 (Discrete Analysis 2022:21).
- Sharpens the Lam–Leung lower bound on the minimal number of terms in a vanishing sum of N-th roots of
  unity (special case). Caps how LOW-weight (= how deep/deficit-small) a vanishing relation can be.
- ROLE: bounds the minimal weight ⟹ bounds the minimal deficit at which a bad config can appear ⟹ caps the
  general-r list size from BELOW the support, but again does NOT bound the level-set count.

### [LIT] Hanson(–Petridis), "Refined estimates concerning sumsets contained in the roots of unity",
arXiv:1905.09134 / PLMS 122 (2021).
- Abstract result: Paley clique <= sqrt(p/2)+1; additive decompositions of the quadratic residues come only
  from co-Sidon sets. Underlying: additive-energy / sumset structure of `mu_d` (d-th roots of unity / QR).
- REGIME: prime field `F_p`; bounds are nontrivial for `|mu_d| = d <~ sqrt(p)` (subgroups SMALLER than sqrt p).
- This is the F_q additive-energy quantity that WOULD bound the collisionCount (= M2 second moment). PAYWALLED
  (Wiley plms.12322) — abstract recovered; the exact `|A||B| <= ...` bound not extracted in-env.

### [LIT] Shkredov, "On additive shifts of multiplicative subgroups", arXiv:1102.1172 (+ common-energy 2025
S0097316525000214).
- E^+(Gamma) for a multiplicative subgroup Gamma of F_p^*: nontrivial energy bounds (Stepanov / char sums);
  the additive-energy and additive-shift-intersection bounds `|Gamma ∩ (Gamma+x)|`.
- REGIME (decisive): prime field `F_p`, and the SHARP regime is `|Gamma| <~ p^{2/3}` (often `|Gamma| ~ sqrt p`);
  for `|Gamma|` near `p^{1-o(1)}` the bounds degrade to trivial. The 2025 common-energy paper gives a
  polynomial small-doubling criterion via common energy of subsets.
- Method (Stepanov) is essentially a PRIME-FIELD tool; over `F_q = F_{p^m}` the bounds are worse and
  conditional. [PAPERS_NEEDED note O30 `SubgroupRepCountFiniteFieldCounterexample`: the char-0 energy
  bound FAILS over F_q — this is flagged as the true obstruction.]

### Recent subgroup partial-char-sum (the missing `subgroup_quadratic_sum_is_partial` input):
- arXiv:2409.13515, arXiv:2502.14436 (Mérai–Shparlinski–Winterhof line; latter improves for 0.13<rho<0.32):
  incomplete/sparse MULTIPLICATIVE character sums over subgroups; sharpest current bounds in the prize
  rho-window. Give `n^{1-nu}`-type savings (BGK regime), `nu` tiny.

================================================================================
## 3. RUTHLESS APPLICABILITY ASSESSMENT — does the literature close the object in the PRIZE regime?
================================================================================

PRIZE regime: faithful/production `q ~ n·2^128` (up to 2^256), `eps* = 2^-128`, deep band (deficit 2),
ground set = the SMOOTH multiplicative subgroup `mu_n`, `n = 2^k`, `n` up to ~256–512. O172: production q
REALIZES the char-0 (faithful) WORST case exactly (saturating envelope; q-independent above q* ~ 2^{n/2}).
So the prize question is: in the FAITHFUL limit, is `#bad(r) <= K = 2^r C(n/2,r)` for all r, all n?

### (A) MSS papers (LMRW, GPP): GROUND-SET MISMATCH — they do NOT apply to mu_n. DECISIVE.
- LMRW ground set `D = g(F_q)` (polynomial image, ~q/deg points); GPP ground set `D = F_q` (full field) or a
  polynomial image. **NEITHER is a multiplicative subgroup.** The mu_n joint count is a count over `n=2^k`
  points (n ~ q^{1/5}, a THIN subgroup), not over ~q points. The diagonal-equation / Li–Wan-sieve machinery
  is built on the variety `V: sum x_i^j = b_j` intersected with `D^k` for `D` a poly image; restricting the
  `x_i` to lie in a subgroup `mu_n` adds the constraints `x_i^n = 1`, turning the system into a sparse
  high-degree complete intersection whose point count is NOT controlled by their estimates. GPP explicitly
  say the method "does not require multiplicative structure" — it also does not EXPLOIT or HANDLE it; their
  D is full-field/poly-image, period.
- (a) They bound the SINGLE-(c1,..,cm) joint count `N_m(k,b)` as `C(|D|,k)/q^m ± error`. Two failures here:
  * the main term `C(|D|,k)/q^m` is the count over `|D| ~ q` points; for `mu_n` the analogous "main term"
    would be `C(n,r+1)/q^2` which is `<< 1` (since `C(n,r+1) << q^2` in the prize regime `q >> n^2`), so the
    "average fiber is empty" — the main-term/error split is VACUOUS for a thin subgroup ground set;
  * the prize object is the e1-axis SUPPORT (`#bad`, a 1-D projection ~ C(n/4,2)·n scale), NOT the per-pair
    count `N2(c1,c2)` (~ O(1)). The MSS theorems bound the wrong moment dimension.
- NON-VACUITY windows also fail outright: LMRW needs `k > 3m_p+1` (here `k=r+1` can be as small as 4, vs
  `m=2`); GPP needs `k <= q^{0.24}` and `m <= (k-25)/50` (with `m=2` this needs `k >= 125`, i.e. `r >= 124`)
  — for the prize's small deficit-2 deep band these windows are nowhere near satisfied. The literature's
  COUNTING regime is `k` large, `m` small relative to `k`; ours is `m=2` FIXED and `k=r+1` ranging from tiny
  to `n/2`, over a THIN subgroup. (b) FAILS in the prize regime on both axes (ground set AND k,m window).

### (B) Vanishing-sums (CDK, Łaba–Marshall, Lam–Leung): EXISTENCE/SUPPORT only, NOT a count.
- These classify WHICH vanishing relations exist (the support of the relation lattice) and bound the
  MINIMAL weight. They are the right tool for "does a deep-band bad config exist at deficit 2" (yes — the
  dyadic weight-2 antipodal atom), but they do **not** count the number of distinct e1 values / the size of
  the joint level-set. They control the numerator's STRUCTURE, not the cardinality #bad. So they (a) bound
  neither the single-e1 count nor the joint level-set magnitude — they are orthogonal (support, not count).

### (C) Additive-energy of subgroups (Hanson–Petridis, Shkredov): WRONG SIZE REGIME — reduces toward/below
###     the trivial bound in the prize window, and is prime-field-biased.
- These bound `E^+(mu_d)` / `|Gamma ∩ (Gamma+x)|` and are the natural control on `collisionCount` (= M2).
  BUT their nontrivial regime is `|Gamma| <~ sqrt(p)` to `~ p^{2/3}` over PRIME fields. The prize regime has
  `n = |mu_n| ~ q^{1/5}` (well below sqrt q), so SIZE is fine — BUT:
  * Over the prize's production fields `F_q` (large, often `q = p` faithful but possibly extension), the
    char-0/prime-field energy bound is flagged FAILING in-tree (O30 `SubgroupRepCountFiniteFieldCounterexample`):
    the clean `E^+(Gamma) << |Gamma|^{2+o(1)}` does not transfer to F_q with controlled constants.
  * Even granting `E^+(mu_n) << n^{2+o(1)}` (the BEST plausible energy bound), it controls `collisionCount`
    for the (sum) p1-statistic, but the JOINT (p1,p2) collision count is a HIGHER-order energy
    `E_{1,2}(mu_n) = #{(a,b,c,d): a+b=c+d, a^2+b^2=c^2+d^2}` for pairs (and the (r+1)-fold analogue for our
    subsets) — this is the `E_r`/additive-energy-of-curves object (PAPERS_NEEDED G2 4th-moment floor
    `E_2 = 3n^2-3n`), whose GENERAL-r form is itself OPEN (Hegyvári arXiv:2602.01781 = freshest, distribution
    only). And via Cauchy–Schwarz the energy gives only `#support >= C(n,r+1)^2 / collisionCount`, a LOWER
    bound on support — the WRONG direction for proving `#bad <= K` (we need an UPPER bound on #bad).
- So (b) the additive-energy route fails in the prize regime: it is prime-field-calibrated, its F_q transfer
  is the documented obstruction, the JOINT higher-order energy is open, and its inequality direction (lower
  bound on support) is opposite to what `#bad <= K` requires. (c) it does NOT reduce to Johnson — it is a
  different (energy) wall, but it is an OPEN wall, not a closure.

### (D) Does it reduce to Johnson? NO — and that is the point.
- The r=3 case is PROVEN unconditionally (closed form, axiom-clean) and gives `#bad = n*C(n/4,2)+1`, which is
  `Theta(n^3)` — WAY below both K (`Theta(n^3)` too, with the 5.33x constant margin) and below any Johnson
  list bound (`O(sqrt(1/eps))`-ish). The deep-band #bad is `poly(n)`, q-INDEPENDENT above threshold — this is
  STRICTLY a sub-Johnson, q-free phenomenon (the whole point of the census/demand route: it does not go
  through Johnson at all). The literature bounds that DO apply (none, in the joint-subgroup regime) would have
  to be `poly(n)` and q-independent. The MSS papers give q-DEPENDENT main+error terms (`C(q,k)/q^m`), which is
  the WRONG shape — a q-dependent bound here is the `O(n)/q` "silent at production budget" family the in-tree
  CLAUDE.md §3.5 already records as non-prize. So the literature, where it applies at all, REDUCES TO the
  q-dependent (pigeonhole/averaging) bound that provably LOSES the factor /q (`ListInteriorQDependenceNoGo`),
  i.e. it is below the resolution needed — not Johnson, but the even-weaker averaging floor.

================================================================================
## 4. THE EXACT GAP
================================================================================

The literature bounds the JOINT m-moment subset-sum count `N_m(k,b)` over `D = F_q` or `D = g(F_q)`
(full field / polynomial image), as a q-dependent main term `C(|D|,k)/q^m` plus a `q^{k/2}`-scale error,
in the window `k` large / `m` small / `k <= q^{0.24}`. The prize object is the e1-axis SUPPORT of the
(e1,e2) joint level-set over the THIN multiplicative subgroup `mu_n` (`n=2^k ~ q^{1/5}`), at FIXED `m=2`
and SMALL `k = r+1`, needing a q-INDEPENDENT `poly(n)` UPPER bound `#bad(r) <= 2^r C(n/2,r)`.

The gap is FOUR-fold and each is fatal on its own:
  1. GROUND-SET: subgroup `mu_n` (n points, `x^n=1` constraints) vs full-field/poly-image (q points).
     No MSS theorem is stated or proven over a multiplicative subgroup ground set. [DECISIVE for LMRW/GPP]
  2. MOMENT-DIMENSION / OBJECT: literature bounds the per-target joint count `N2(c1,c2)` (~O(1), and its
     main term is `<<1` hence vacuous for thin G); prize needs the 1-D e1-axis SUPPORT projection (~Theta(n^3)
     at r=3), a different functional of the same level-set.
  3. PARAMETER WINDOW: literature needs `k` large, `m << k`, `k <= q^{0.24}`; prize is `m=2` FIXED,
     `k=r+1` from 4 up to `n/2`, deep (small-deficit) band — outside every stated window.
  4. q-DEPENDENCE / RESOLUTION: literature bounds are q-dependent (`/q^m`, `q^{k/2}` error); prize bound is
     q-INDEPENDENT `poly(n)` (O172: faithful = worst case). The q-dependent route provably loses /q
     (`ListInteriorQDependenceNoGo`), so even where applicable it is below the needed resolution.

The additive-energy route (Hanson–Petridis / Shkredov) is the ONLY one whose object (energy = collisionCount)
is the right q-free shape, but: it is prime-field-calibrated with a documented F_q-transfer failure (O30); the
JOINT higher-order energy `E_{1,2}` (the (p1,p2) collision count) is itself OPEN (no general-r bound; only the
4th-moment `E_2=3n^2-3n` floor is known, Duke–Garcia G2); and Cauchy–Schwarz gives a LOWER bound on support,
the WRONG direction for `#bad <= K`.

VERDICT [HONEST, not a closure]: The general-r (r>=4) deep-band #bad-scalar bound `#bad <= K` does NOT
follow from the moment-subset-sum literature (LMRW, GPP) — ground-set, object, window, and q-dependence all
mismatch in the prize regime. It is also not delivered by the vanishing-sum classification (CDK,
Łaba–Marshall: existence/support, not count) nor by the additive-energy literature (Hanson–Petridis,
Shkredov: wrong size/field regime, open joint higher-order energy, wrong inequality direction). The object
**REDUCES TO an OPEN problem**: a q-independent upper bound on the e1-axis support of the (e1,e2) joint
level-set (equivalently a usable upper bound on the JOINT higher-order additive energy `E_{1,2}`) over a thin
2-power multiplicative subgroup over the production field — which the published literature does not contain.
Per the $1M CLOSED requirement: this is a REDUCES-TO-OPEN finding, NOT a solution. r=3 stays the only PROVEN
rung; r>=4 stays the named open analytic core (ExcessCensusLaw), with all-n MEASURED margins 2.46x–20.1x as
the only evidence, and production q = worst case [PROVEN-direction-of-transfer, O172] as the only structural
reduction in hand.
