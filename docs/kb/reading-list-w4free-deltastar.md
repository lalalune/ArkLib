# W4-free δ* — reading list & honest resolution (#407)

Five recent papers most relevant to a **W4-free** pin of δ* (avoiding the worst-case incomplete
character sum `max_b|Σ_{x∈μ_n} e_p(bx)| ~ √(n log(q/n))`, the BGK/Bourgain 25-year-open wall).
Compiled by a multi-agent research workflow (13 agents, 2026-06-13).

1. **Crites & Stewart, "On Reed–Solomon Proximity Gaps Conjectures" (2025)** — eprint 2025/2046,
   STOC 2026. Proves the up-to-capacity (1−R) conjecture FALSE in all three forms (correlated
   agreement, WHIR mutual-CA, deep-FRI list-decodability); modifies the pin to
   δ* = 1 − H_q(δ) − 1/n − η — structurally identical to the in-tree δ* = 1−ρ−H(ρ)/(β log₂ n);
   gives the CA-error↔list bridge L = O(εq) matching the budget q·ε* ≈ n.

2. **Goyal & Guruswami, "Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed–Solomon
   Codes" (2025)** — ECCC TR25-166 / eprint 2025/2054. THE live W4-free mechanism: reaches 1−R−η at
   LINEAR field size O_η(n) via a curve-pruning local property ("curve/V-decodability") that
   EXPLICITLY avoids character sums — but only for RANDOM evaluation points; transfer to fixed
   dyadic μ_n is the open prize gap. (Supersedes withdrawn arXiv 2601.10047.)

3. **Ben-Sasson, Carmon, Habock, Kopparty & Saraf [BCHKS25], "On Proximity Gaps for Reed–Solomon
   Codes" (2025)** — ECCC TR25-169 / math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf. A genuine
   second-moment/variance concentration argument on subspace-polynomial roots that reaches ONLY
   Johnson (1−√ρ) — demonstrating pure concentration on this object recovers exactly the √n deficit.

4. **Brakensiek, Gopi & Makam, "Generic Reed–Solomon Codes Achieve List-Decoding Capacity" (2022/23)**
   — arXiv:2206.05256 (+ Brakensiek–Dhar–Gopi, "Improved Field Size Bounds for Higher-Order MDS
   Codes," ISIT 2023, arXiv:2212.11262). The algebraic route: higher-order MDS(ℓ) ⟺ generalized-
   Singleton list bound via GM-MDS zero-patterns (no character sums); BUT the field-size lower bound
   q ≥ C(n−2,k−1) ≈ 2^{nH(ρ)} provably EXCLUDES the prize regime q = n^β.

5. **Alrabiah, Guo, Guruswami, Li & Zhang, "Random Reed–Solomon Codes Achieve List-Decoding Capacity
   with Linear-Sized Alphabets"** — arXiv:2304.09445 (Advances in Combinatorics). Capacity list-size
   for random RS at linear field size via probabilistic zero-pattern analysis — the object that must
   be derandomized to the explicit dyadic domain.

Companion survey: **Arnon–Boneh–Fenzi, "Open Problems in List Decoding and Correlated Agreement"**
(eprint 2026/680).

## 2026 refresh items for #407

- **Krachun, Kazanin & Habock, "Failure of proximity gaps close to capacity"** — eprint 2026/782.
  This is the current identifier for the near-capacity failure lane; do not confuse it with the
  Goyal--Guruswami positive folded/subspace-design/random-RS lane.
- **Antonio Kambire, "Proximity Gaps Conjecture Fails Near Capacity over Prime Fields"** —
  arXiv:2604.09724. Gives a self-contained prime-field version of the Krachun--Kazanin sketch:
  a family of prime-field RS codes with failure at radius `1 - k/n - Omega(1 / log n)`. This is a
  high-priority read for the #407 upper-bracket / Kambire edge formalization path, but it is still a
  near-capacity failure construction rather than a closed delta-star pin for the smooth dyadic
  prize regime.
- **Chen Yuan & Ruiqi Zhu, "A Syndrome-Space Approach to Proximity Gaps and Correlated Agreement
  for Random Linear Codes"** — arXiv:2605.07595. Gives a direct parity-check / syndrome-space proof
  of proximity gaps and correlated agreement for random linear codes, conceptually separating the
  mechanism from list decoding in the random-code ensemble. Watch for reusable syndrome-space
  witness reductions, but this does not settle fixed smooth Reed--Solomon domains.
- **Fernando Granha Jeronimo, Lenny Liu & Pranav Rajpal, "Optimal Proximity Gap for Folded
  Reed--Solomon Codes via Subspace Designs"** — arXiv:2601.10047. Proves up-to-capacity proximity
  gaps for folded RS/subspace-design codes via line stitching, pruning, and affine lifting. Useful
  for transfer machinery and for separating folded-code capacity mechanisms from the fixed smooth
  RS delta-star obstruction.
- **"Explicit Constant-Alphabet Subspace Design Codes"** — arXiv:2604.15218. Relevant to the
  subspace-design / curve-decodability transfer path: it records that subspace-design structure
  implies curve decoding and hence proximity-gap/correlated-agreement consequences in the
  folded/subspace-design world. This is a transfer input, not a plain fixed-domain RS delta-star
  closure.

## Honest resolution (W4-free question)
- The imprimitive 2-power-tower monomial lines fold SELF-SIMILARLY W4-free (even/odd code split,
  geometric telescope to ~n/2 < budget). But every fold bottoms out on a PRIMITIVE base line, and
  primitive-line incidence = RS[k+1] list size on a full subgroup = non-principal eigenvalue of
  Cay(F_q,μ_m) = **W4** (Paley-graph object). The "primitive lines concentrate" premise IS the
  unproven square-root cancellation.
- The ALGEBRAIC higher-order-MDS route provably CANNOT pin at prize field size (needs q ≥ 2^{nH(ρ)};
  μ_n fails MDS(3) via antipodal sum-zero pairs — `HigherOrderMDSOrderThreeFail`).
- The LIVE combinatorial W4-free route (fleet, `FactorizationRigidity.lean`): δ* = the q-independent
  COSET-SUMSET count at the extremal monomial direction (Kambiré edge δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*),
  UPPER bracket proven). Lower-bracket optimality reduces to 4 combinatorial pieces; (2) coset-
  saturation ("beyond Johnson, every large agreement set is a μ_d-coset") and (4) Kambiré sumset-max
  (#bad = |H^{(+r)}| = distinct r-subset-sums of μ_s) are W4-free, verified-not-proven.
- **Verdict: no closed W4-free pin in the prize window interior yet.** The escape exists in the
  literature (GG25) only for random points; the irreducible open step is the transfer to fixed μ_n.

## 2026-06-14 — papers for the No-Excess / generalized-Vandermonde-faithfulness reduction

The prize δ* lower bound reduces (this session) to: **is the rank-deficiency locus of the
generalized Vandermonde over μ_{2^μ} char-independent at proper primes q≡1 mod n** (= bad-subset
set identical char-0 ↔ F_q, = char-p bad-count ≤ char-0 count). bad-T ⟺ Schur_λ(ζ^T)·Vandermonde=0;
Vandermonde is 2-power-safe (Norm(1−ζ^d)=2-power), so it reduces to faithfulness of Schur_λ(ζ^T)=0.
PROVEN for n=8 (no ≡1-mod-8 factors) and n=16 (only ≡1-mod-16 factor of Norm(h_5) is 17=full group),
but REFUTED-as-general at n=32 (Norm(h_11) has many ≡1-mod-32 factors: 97,193,…). Relevant literature:

1. **Evans–Isaacs, "Generalized Vandermonde determinants and roots of unity of prime order"** —
   Chebotarëv's theorem: for PRIME p, ALL minors of (ζ^{ij}) are nonzero (so prime-order subgroups are
   trivially char-faithful). The prize is the PRIME-POWER (2^μ) generalization where minors DO vanish.
   (semanticscholar b4ed6b761b...)
2. **"The Schur polynomials in all primitive nth roots of unity" (arXiv:2403.10817)** — Thm 1.1:
   for n with ≤2 distinct odd prime factors (⊇ all 2-powers), s_λ(all primitive nth roots)∈{−1,0,1}
   (norm ≤1 ⟹ no spurious vanishing on the FULL primitive-root set). Promising special case; does NOT
   cover arbitrary w-subsets (where norms grow, e.g. 877313 at n=32). "number two is essential".
3. **arXiv:2310.09992** — nonvanishing-minors (NVM) of the compressed subgroup Fourier matrix,
   characterized by a Gauss-sum nonvanishing condition; solved index 2,3; LARGE INDEX OPEN = exactly
   our 2^μ ⊊ F_q* faithfulness wall.
4. **"Skew Schur polynomials and cyclic sieving phenomenon" (arXiv:2112.12394)** + **skew hook
   (arXiv:2211.14093)** — combinatorial (ribbon-tableaux) VANISHING criteria + factorization for
   specialized skew Schur at roots of unity. The route to a field-independent vanishing criterion;
   covers principal specialization (consecutive powers), needs extension to arbitrary subsets.
5. **"Polynomials arising in factoring generalized Vandermonde determinants" (di.univr.it allegato700388)**
   + ACTA ARITH XCV.2 "Generalized Vandermonde determinants" — factoring genVandermonde = Vandermonde·Schur,
   the structural identity underlying the 2-power-safe split.

## 2026-06-14 (turn 2) — the reduction lands on the recognized GENERICITY gap of RS list-decoding

Literature confirms the δ* prize reduces EXACTLY to the open explicit/non-generic RS list-decoding gap:
the BGM-type genericity condition (intersection/Vandermonde determinants nonzero), specialized to the
explicit dyadic subgroup μ_{2^μ}, IS the generalized-Vandermonde/Schur values that VANISH for μ_n
(= the bad-subset/Schur-vanishing of this session). So μ_{2^μ} is provably NON-generic for BGM; the
capacity results do NOT transfer. Papers:

6. **Brakensiek–Gopi–Makam, "Generic Reed-Solomon codes achieve list-decoding capacity" (STOC'23,
   arXiv:2206.05256)** — generic RS is (1−R−ε, O(1/ε))-list-decodable; proof needs genericity
   (Schwartz–Zippel on intersection matrices). The genericity determinants = the μ_n Schur values.
7. **"Random/Randomly-Punctured RS achieve LD capacity, linear/poly alphabets" (arXiv:2304.09445,
   updated Aug 2025)** — RANDOM evaluation points; the prize's μ_n is a SPECIFIC (non-random) set.
8. **"Explicit Subcodes of RS that efficiently achieve LD capacity" (arXiv:2401.15034)** — explicit, but
   SUBCODES (tensor + cyclic shift), NOT plain RS on μ_n.
9. **"Explicit Folded RS and Multiplicity Codes Achieve Relaxed Generalized Singleton Bounds" (STOC'25)**
   — FOLDED RS, not plain RS (FRS≠RS, the JLR26 route doesn't transfer, see [[arklib-389-jlr26-frs-research-map]]).
10. **"List-decoding RS up to the Singleton bound" + "Efficient LD of Polynomial Ideal Codes optimal list
    size" (arXiv:2401.14517)** — algorithmic, generic/ideal-code structure, not the explicit μ_n point set.

VERDICT: no 2023–2026 result list-decodes PLAIN RS on the explicit multiplicative subgroup μ_{2^μ} in the
window. The prize's positive direction = closing this genericity gap for μ_n (the Schur-vanishing is the
explicit obstruction). OPEN. My reduction is the correct map onto it; the closed δ* = Kambiré edge is
exact iff μ_n's Schur values don't vanish "too much" at the prize prime (the open NVM, = this gap).

## 2026-06-14 — NVM / Chebotarev route to the prize index: literature is a hard NO, but a NEW char-0 structure invariant (reflection-symmetry) found

GOAL of this turn: extend Chebotarev/NVM (which settles prime-order subgroups — all minors nonzero —
and index 2,3) to the prize index 2^μ, and find a STRUCTURE THEOREM for exactly which generalized-
Vandermonde / Schur (h_j) minors of μ_{2^μ} vanish.

### Literature verdict (read in full)
- **arXiv:2310.09992** ("uncertainty principle for small-index subgroups", Garcia–Karaali–Katz lineage):
  the NVM property they characterize is for the COMPRESSED Fourier matrix (whole-subgroup symmetry),
  via a Gauss-sum condition — and it is ALL-OR-NOTHING (does NVM hold or not), with NO per-minor
  vanishing-locus structure theorem. Index 2 = [ref 7] Gauss-sum-of-extensions condition; index 3 =
  Thm 3.2 (NVM ⟺ T₀=∑Gᵢ≠0 and Gᵢ≠Gⱼ), tractable ONLY because ζ₃²+ζ₃+1=0 collapses the 3×3 to a
  circulant. Remark 3.4 explicitly leaves index ≥4 OPEN; the circulant collapse does NOT exist for
  2-power index. So this route gives the prize index NEITHER all-nonzero NOR a vanishing structure.
- **arXiv:2403.10817** ("Schur polynomials in all primitive nth roots of unity"): s_λ ∈ {−1,0,1} for n
  with ≤2 distinct odd prime factors (⊇ all 2-powers), via unimodular/maximal-circuit machinery. But it
  (i) covers ONLY the full primitive-root set, NOT arbitrary w-subsets/cosets (the prize object), and
  (ii) gives NO criterion for WHEN the value is 0 vs ±1 — the authors call the vanishing question open.
- **Lam–Leung "Vanishing sums of roots of unity"** + **arXiv:1503.07281 "vanishing power sums"**: give the
  COMPLETE structure theorem ONLY for the e_1 / power-sum p_k face (for p=2: vanishing ⟺ disjoint union
  of antipodal pairs {t, t+n/2}, count C(n/2, w/2)). NEITHER addresses h_j / Schur for j≥2.
  CONCLUSION: no paper in the literature gives a vanishing-locus structure theorem for h_j/Schur minors
  of arbitrary subsets of μ_{2^μ}. The prize object is genuinely outside the published NVM/Chebotarev
  and vanishing-sum literature. The 2-power index helps ONLY the e_1 face (Lam–Leung), not the deep h_j.

### NEW structural result this turn (probes /tmp/nvm_*.py, /tmp/refl_charp.py; n=8,16,32 exhaustive)
A char-0 vanishing minor of μ_{2^μ} (worst genuine direction, NO wraparound j+w−1<n) is one of:
  (P) **antipodal-union** (the Lam–Leung e_1 face: disjoint {t,t+n/2} pairs), OR
  (I) **imprimitive**: all index-differences even ⟹ T lies in a μ_{n/2} coset, a self-similar 2-adic
      dilation of a smaller vanishing (recurse down the 2-tower to base case = antipodal pairs).
  REFINED INVARIANT: EVERY char-0 no-wraparound vanishing T is **REFLECTION-SYMMETRIC** (T = c−T mod n
  for some center c) — verified 100% at n=8,16,32 for h_1,h_2,h_3,w=4. (Necessary; antipodal-union and
  imprimitive both imply it.) This dihedral closure is the candidate clean char-0 structure rule.

### The CHAR-P discriminator (the crux, measured n=32 at prize-shaped primes q≡1 mod 32)
At n=8 the Schur-vanishing SUBSET locus is FULLY char-faithful (q=17,41,...,4129 all match char-0).
At n=32 it DEVIATES HEAVILY at small bad primes: per (h_j,w=4), 32–384 EXTRA subsets vanish mod q
(q=97,193,257,...) beyond char-0. CLEAN SEPARATION: char-0 vanishings are 100% reflection-symmetric;
the char-p extras are 0–9% reflection-symmetric (q=193,257: 0%). So reflection-symmetry / dihedral
closure is a SHARP characteristic discriminator: the char-faithful core is exactly the reflection-
symmetric (Lam–Leung ⊕ imprimitive-tower) set; the char-p excess is the structureless, prime-specific
remainder. This is the algebraic shape of the open char-p excess — it is NOT a clean count, it tracks
which q≡1 mod n divide the (non-2-power-safe) Schur norm Norm(h_j(ζ^T)).

HONEST NET (no closure): the NVM/Chebotarev literature does NOT pin the prize index — it gives neither
all-nonzero (false for 2^μ) nor a vanishing structure theorem (only e_1 face is settled, by Lam–Leung).
The new contribution is the reflection-symmetry invariant cleanly separating char-faithful core from
char-p excess, but the excess at the SUBSET level is large and structureless at n=32. OPEN. (Caveat:
the SUBSET-level excess need not promote the deployed distinct-bad-SCALAR count at GOOD bands — the
issue's collision-capping/cliff-confinement claim — which my probes could not resolve at n=32 because
the deep-band scalar enumeration is computationally out of reach; that scalar-level faithfulness, not
subset-level, is the actual prize gate and remains the open input.)

## 2026-06-14 — R-THIN via the SPARSE-POLYNOMIAL-ON-ROOTS-OF-UNITY literature (fewnomial / vanishing-sums)

R-thin reformulated (issue #407 sparse-poly form): `P(x)=x^a+γx^b−c(x)`, `deg c < k`, is a
`(k+2)`-term (`t`-sparse, `t=k+2`) polynomial; `S = {x∈μ_n : P(x)=0}` (`n=2^μ`) is the agreement
set of a monomial line vs a single deg-`<k` codeword. Claim was: every "genuinely ragged" `S`
(not a `μ_{d'}`-coset-union) has `|S| ≤ √(nk)` (Johnson). The relevant body of work is the
**fewnomial-roots-of-unity / vanishing-sums** literature (NOT a character-sum estimate):

1. **Beukers–Smyth, "Cyclotomic points on curves"** (Number Theory for the Millennium I, 2002;
   webhomes.maths.ed.ac.uk/~chris/preprints/beukers_smyth.pdf). MAIN THEOREM: a plane curve
   `f(x,y)=0/ℂ` has either `≤ 22·V(f)` cyclotomic points (`V` = Newton-polytope area; sharper
   `4V` non-reciprocal; Bézout-equivalent `11(deg f)²`) **or infinitely many, the latter iff `f`
   has a factor `xⁱyʲ−ω`** (a torsion coset). So roots-of-unity solutions split as
   **(finitely many ISOLATED points) + (families on torsion cosets `xⁱyʲ=ω`)** — EXACTLY the
   R-thin "ragged-minus-coset vs coset-union" dichotomy. §2 gives the univariate cyclotomic-part
   algorithm. THE structural source for R-thin.

2. **Mann, "On linear relations between roots of unity"** (Mathematika 12, 1965) + **Conway–Jones,
   "Trigonometric diophantine equations (on vanishing sums of roots of unity)"** (Acta Arith. 30,
   1976). A NON-DEGENERATE vanishing relation `Σ_{e∈T} c_e ω^e = 0` (no proper subsum vanishes)
   forces all `ω^e` to be `d`-th roots with `d = ∏ pᵢ`, `Σ(pᵢ−2) ≤ |T|−1` (Conway–Jones; Mann:
   `pᵢ ≤ |T|`). **For `μ_n`, `n=2^μ`, the only prime is 2 ⟹ the only minimal 2-power relation is
   `z+(−z)=0`** — every structured (coset) part is antipodal-built (matches in-tree
   `LamLeungTwoPow`/`LamLeungMultisetAntipodal`, `W(2^μ)=ℕ·2`). The non-antipodal mass is the
   isolated part.

3. **Schlickewei (1996) / Evertse, "The number of solutions of linear equations in roots of unity"**
   (Acta Arith. 89, 1999; pub.math.leidenuniv.nl/~evertsejh/98-roots.pdf). DECISIVE BOUND: the
   number of NON-DEGENERATE solutions of a `t`-term equation `a₁x₁+···+a_tx_t=0` in roots of unity,
   for **arbitrary COMPLEX coefficients** (char 0), is `≤ (t+1)^{3(t+1)²}` (Evertse's exact constant;
   exponent `3` improvable to `2+ε`; Mann/Conway–Jones give `≤ e^{c·t}`-type variants for ℚ-coeffs)
   — **depending ONLY on `t` = the number of terms, NOT on the order `n` of the roots.** For R-thin
   `t=k+2`, so the isolated count is `≤ (k+3)^{3(k+3)²}`, n-independent. The citable theorem behind
   R-thin's isolated part.

### Verdict: the literature REFUTES R-thin as literally stated, but SHARPENS the correct quantity
- **Literal R-thin is FALSE** (char-0 numerics, exact, n=8,16): a set `μ_8 ∪ {one extra point}`
  (`|S|=9` at `n=16,k=2`) is "ragged" by the strict not-a-pure-coset-union definition yet exceeds
  `√(nk)=5.66`. Mechanism: the binomial `x^a+γx^b` vanishes on a large coset family, the deg-`<k`
  part adds a few isolated points; "coset ∪ few points" is wrongly classified ragged.
- **The CORRECT R-thin = Beukers–Smyth isolated part** (S minus all maximal `μ_d`-coset families).
  Char-0 numerics (exact `n≤16`, sampled `n≤128`): the isolated count is **`n-INDEPENDENT`** —
  fixed `k=2,3` give isolated `=4` flat across `n=16→128` (while `√(nk)` grows). At rate `ρ=k/n`
  the isolated count scales `~2k–1` (linear in `k`, indep of `n`), `≪ √(nk)` for `n≫k`. This is
  exactly the Schlickewei/Evertse degree-independence and is **STRONGER than Johnson** in the thin
  (prize) regime.
- **But NO usable explicit constant.** Evertse's `k^{3k²}` is astronomical vs the prize budget
  `q·ε*≈n`; Mann/Conway–Jones constants are likewise exponential in `k`. So the literature gives
  the right SHAPE (term-count-bounded, n-independent ragged part) and the right STRUCTURE
  (coset+isolated, antipodal-only cosets at `2^μ`) but does not deliver the tight `≤budget` bound
  the lower bracket needs at prize rate `k=n/4` — there the measured `~2k=n/2=√(nk)` coincides with
  Johnson and the constant must come from the realizability/Hankel (single-deg-`<k`) constraint the
  count-level theory discards (consistent with the issue's "realizability is the live lever").

### SHARP isolated constant for OUR Newton polytope `{0..k−1, a, b}` (2026-06-14, EXACT)
The task was to specialise the Beukers–Smyth *sharp* isolated bound to our actual support and read
off the constant — is it `≤ 2k`, `≤ budget ~ n`, or over budget? **Resolved EXACTLY.**

- **Dimensional caveat (load-bearing, must be stated).** Beukers–Smyth `22V(f)` / `4V` / `11(deg f)²`
  is a **TWO-variable** plane-curve theorem; `V` is the **AREA** of a 2-D Newton polytope. Our object
  `P(x)=x^a+γx^b−c(x)` is **ONE-variable** — its Newton polytope is a segment of **area 0**, so the
  `22V` bound is *vacuous/inapplicable* as stated (consistent with `Xⁿ−1` having all `n` roots
  cyclotomic). The Aliev–Smyth restatement (Lemma 2.2: "curve `C` has `≤ 22 vol₂(g)` ISOLATED torsion
  points", and `≤ 11(deg f)²` for `f∈ℂ[X,Y]`) confirms `22V` counts the **isolated** part — but only
  in **2 variables**. The 1-variable isolated count is governed by **degree / term-count**, not area.
- **EXACT worst-case isolated count = `k+1`** (NOT `~2k−1`, NOT Evertse `k^{3k²}`). Full exact sweep
  over all realizable `S` (integer `ℤ[ζ_n]` arithmetic, `ζ^{n/2}=−1`, exact zero test;
  `/tmp/probe_iso4.py`, `/tmp/probe_final.py`) gives the extremal witness = the **consecutive run**
  `S = {ζ⁰,ζ¹,…,ζ^k}` (`k+1` points): `Q_S=∏(X−ζ^j)` has dense support `{0,1,…,k+1}` (degree `a=k+1`,
  `b=k`, codeword part `{0..k−1}`), so it IS realizable as the `(k+2)`-sparse line, and the run shares
  no nontrivial `μ_d`-coset ⟹ **all `k+1` points are isolated**. Verified `n=8,16,32,64,128`,
  `k=2..5`: isolated `= k+1` whenever `k+1 < n/2` (above that the antipodal coset starts folding the
  run into the core, *lowering* the isolated count). **n-INDEPENDENT, value `k+1`.**
- **Is it sub-budget?** YES, trivially: `k+1 = ρn+1 ≤ n ≈ ε*q = budget` at every prize rate
  (`ρ∈{1/2,1/4,1/8,1/16}`) and every `n` (`/tmp/analysis_newton.py`). So the **per-direction isolated
  excess is sub-budget by a clean elementary bound `k+1`, no Evertse, no `22V`, no BGK.**
- **WHY this does NOT close R-thin / δ\* (the decisive scope gap).** The `k+1` bound is the isolated
  size of `S` for **ONE fixed `(a,b,γ,c)`**. The δ\* budget `ε*q≈n` bounds a **DIFFERENT** object:
  the number of **bad scalars `γ`** for a fixed direction (= the far-line *incidence* / interleaved
  list size; in-tree `epsMCA_ge_far_incidence`, `MCAWitnessSpread`). Via the in-tree Vieta pin
  (`γ=−Σ_{ζ∈S}ζ`) the bad-`γ` set equals the **distinct `r`-fold subset-sum** `|S^{(+r)}|` of the
  isolated/coset roots at `r≈log q` — and bounding THAT by `≈n` is **exactly BCHKS Conjecture 1.12
  (plain RS, s=1)**, the recognized-open subgroup-sumset conjecture (`SubgroupSumsetConjecture.lean`).
  So the Beukers–Smyth split feeds the *structure* (coset-core carries δ\*, isolated part is `O(k)`,
  sub-budget) but the **prize-tight constant lives one level up**, in how isolated points combine into
  the bad-scalar sumset — which Beukers–Smyth/Schlickewei–Evertse do **not** control (they bound the
  agreement SET, not the sumset of its roots over varying directions). **No closure; clean reduction.**

### Probes (char-0 exact + sampled): `/tmp/probe_iso{2,3,4}.py`, `/tmp/probe_final.py`, `/tmp/analysis_newton.py`; older `/tmp/rthin_*.py`, `/tmp/isolated_*.py`
Honest net: the sparse-poly route is the RIGHT framing (the ragged/coset dichotomy IS Beukers–Smyth
isolated/torsion-coset; the n-independence IS Schlickewei–Evertse) and improves the demand-side
characterization from `√(nk)` to a term-count-bounded n-independent ragged count — but supplies no
prize-tight constant. Companion open input unchanged: realizability + char-p transfer of the count.
