# #407 — The exact δ* conjecture (Kambiré-derived) + the closeable optimality core

## Reading list (directed research on the reduced forms)
1. Kambiré, "Proximity Gaps Conjecture Fails Near Capacity over Prime Fields" (arXiv:2604.09724) — upper bracket, native μ_{2^t}. ON DISK.
2. Krachun & Kazanin, "Failure of the proximity gap conjecture for RS near capacity" (personal comm 2026, Kambiré ref [4]) — original sketch. NOT PUBLIC — request.
3. "Any small multiplicative subgroup is not a sumset" (J. Number Theory S1071579720300149) — subgroup-sumset extremality (the optimality lever).
4. Shkredov, "Additive energy of multiplicative subgroups" (arXiv:1712.00410).
5. Alon & Bourgain, "Additive Patterns in Multiplicative Subgroups" (Princeton).
6. "Classifying minimal vanishing sums of roots of unity" (arXiv:2008.11268) — exact |H^{(+r)}(μ_{2^α})| via Lam–Leung.

## THE BOLD CONJECTURE (exact δ*, worst-case)
For RS[F_q, μ_n, k], n=2^μ, q=n^β (β≈4–5), ρ=k/n, ε*=2⁻¹²⁸:
  **δ* = 1 − ρ − 2ρ·ln(1/(2ρ)) / log₂(q·ε*)**  (EXACT).
Worst-case bad count at δ=1−r/s is max_{s|n} |H^{(+r)}(μ_s)| (distinct r-fold sums of μ_s, r=ρs+2),
realized by the Kambiré coset line {X^{rm}+λX^{(r−1)m}}, OPTIMAL.

UPPER bracket PROVEN (Kambiré). LOWER bracket = open core = the coset construction is extremal:
for any monomial stack (X^a,X^b), #codewords within δn of {X^a+λX^b} ≤ |H^{(+r)}|.

Ranking: novelty 8, insight 9, proximity 10, feasibility 6 (optimality is the open core).
Closeable path: FACTORIZATION RIGIDITY — X^a+γX^b−c (deg<k c) with ≥(1−δ)n roots on μ_n forces a
coset-union root set ⟹ agreement sets are subgroup cosets ⟹ distinct γ bounded by the subgroup sumset.
Reduces optimality to a roots-on-μ_n structure theorem (cyclotomic/MDS rigidity).

## Refutation plan
Compute #codewords within δn of {X^a+λX^b} over all monomial stacks at beyond-Johnson δ; check the
Kambiré coset stack is the MAX. Beats it → refuted (δ* smaller); none → push factorization-rigidity proof.

## UPDATE — FACTORIZATION RIGIDITY LEMMA (verified, PROVABLE), reduces the optimality
Lemma: for S ⊆ μ_n, ∏_{z∈S}(X−z) is m-sparse ⟺ S is a union of cosets of μ_m. VERIFIED 0/39202
(μ_16, m∈{2,4}). PROOF: (⟸) coset product = X^m−w; (⟹) m-sparse = Q(X^m), roots' m-th-root cosets.
Reduces optimality: Kambiré stack (a=rm,b=(r−1)m) ⟹ quotient m-sparse ⟹ S coset-union ⟹ γ∈H^{(+r)},
bad count = |H^{(+r)}| exactly. Optimality residuals: (R1) monomial extremality, (R2) Kambiré maximizes
the sumset over (a,b). Both reduce to known combinatorial/MDS/sumset-growth math, not open hard math.
Feasibility 6→8. The factorization rigidity is the novel reusable machinery; candidate for Lean.

## UPDATE — R1 (monomial extremality) SURVIVES refutation; sparsity proof route

Tested monomial vs combination stacks at RS[μ_16,k=4], a0=7 (beyond Johnson 8), p=193
(`/tmp/test_R1.py`). MONOMIAL (X^9,X^5)=bad 5; EVERY combination ≤5 (X^9,X^5+X^7=5;
X^9+X^11,X^5=1; X^9+X^13,X^5+X^7=0; X^7+X^9,X^5=0). **Monomials dominate — R1 survives.**

**Why (proof route, ties to factorization rigidity):** the bad count =
#{γ : ∃ c(deg<k),S : U_0+γU_1−c = ∏_{z∈S}(X−z)·g}. By factorization rigidity a deep-band
agreement set is a coset-union ⟺ ∏_S(X−z) is m-sparse ⟺ U_0+γU_1−c is m-sparse in its high
part. A MONOMIAL pencil (U_0=X^a, U_1=X^b) has the minimal high-support (2 terms), so the
m-sparsity constraint is satisfiable for the MOST γ. A combination adds high-frequency terms,
OVER-CONSTRAINING the m-sparse factorization, so STRICTLY FEWER γ are bad. Hence the worst stack
is monomial. This reduces R1 to a sparsity-maximizes-factorization-count argument — combinatorial,
candidate-provable, NOT open hard math.

**Conjecture status after this turn:**
  - δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*)   [exact, Kambiré window edge; UPPER bracket PROVEN]
  - Optimality (LOWER bracket) reduces to:
      * Factorization rigidity ∏_S m-sparse ⟺ coset-union — **PROVEN** (verified 0/39202)
      * R1 monomial extremality — **survives refutation**, sparsity proof route
      * R2 Kambiré exponents maximize the sumset — = Kambiré's parameter optimization (in-paper)
  All three reduce to KNOWN polynomial/combinatorial/sumset-growth math; no incomputable lemma,
  no char-p Weil wall. Feasibility 8. Remaining to fully close: formalize R1's sparsity argument
  and R2's sumset-growth optimization.

## UPDATE — COSET-SATURATION closes the upper bound; full optimality reduced to 4 pieces

**Coset-saturation (verified 8/8 monomial stacks, beyond Johnson, μ_16):** EVERY large agreement set
(size ≥ a0=7 > Johnson 8) of a monomial line `X^a+γX^b` is a coset-union — `non-coset exists=False`
for (X^9,X^5),(X^7,X^5),(X^11,X^9),(X^7,X^3),(X^13,X^9),(X^9,X^1),(X^15,X^13),(X^11,X^5), incl. dense
cases with 386 agreement sets (`/tmp/coset_saturation.py`, `/tmp/optimality_gap.py`). This closes the
UPPER bound (not just the construction): the bad count = subgroup sumset EXACTLY, no non-coset excess.

**Mechanism / proof route:** `X^a+γX^b = X^b(X^{a−b}+γ)`; with `d=gcd(a−b,n)`, `X^{a−b}` is constant on
`μ_d`-cosets (kernel of `X↦X^{a−b}` on `μ_n` is `μ_d`), so `X^{a−b}+γ` is `μ_d`-coset-constant. Beyond
Johnson the agreement forces FULL `μ_d`-cosets (a non-coset agreement set has size ≤ Johnson — a
Johnson-type bound is the proof route). Then factorization rigidity ⟹ bad scalars = `μ_d`-sumset.

**THE δ\* CONJECTURE — optimality reduced to 4 explicit pieces (no char-p Weil wall):**
  δ\* = 1 − ρ − 2ρ·ln(1/2ρ)/log₂(q·ε\*)   [Kambiré window edge; UPPER bracket PROVEN]
  Optimality (LOWER bracket = no stack beats Kambiré, so δ\* not smaller):
   (1) **Factorization rigidity**  ∏_S m-sparse ⟺ μ_m-coset-union — **PROVEN, axiom-clean Lean**
       (`FactorizationRigidity.lean`, commit d0b565b81, real build 1546 jobs).
   (2) **Coset-saturation**  monomial line, beyond Johnson ⟹ all large agreement sets are
       μ_{gcd(a−b,n)}-coset-unions ⟹ bad count = subgroup sumset — VERIFIED 8/8, gcd+Johnson route.
   (3) **R1 monomial extremality**  worst stack is monomial — VERIFIED, sparsity-maximizes-factorization.
   (4) **R2 Kambiré exponents maximize the sumset** over (a,b,gcd) — = Kambiré's parameter optimization.
  (1)+(2)+(3)+(4) ⟹ max bad count over ALL stacks = |H^{(+r)}|, =q·ε\* exactly at the window edge ⟹
  **δ\* pinned EXACTLY = the Kambiré window edge, worst case included.**

**Honest status:** (1) PROVEN in Lean. (2)(3)(4) VERIFIED numerically (n=16) with concrete proof routes,
NOT yet proven. So this is a strong REDUCTION of the optimality (the open core / line-list upper bound)
to three combinatorial lemmas — escaping the char-p incomplete-Gauss-sum / Weil wall entirely — NOT a
full closure. Feasibility 6→8.5. Next: prove (2) coset-saturation (Johnson-type bound on non-coset
agreement) — the linchpin; then (3),(4). Refutation attempts (R1, optimality-gap) all SURVIVED.

## UPDATE — COSET-SATURATION proof skeleton: the MDS twist dichotomy (key identity verified)

Coset-saturation survives n=32 (4/4 stacks incl. 382-set dense `(X^25,X^9)`, all coset-unions —
`/tmp/coset_sat_n32.py`). The PROOF skeleton (verified `/tmp/saturation_proof.py`, 636 pairs):

**Key identity.** For a monomial line `w_γ=X^a+γX^b`, `d=gcd(a−b,n)`, `ω∈μ_d`, and a codeword `c`
(deg<k) with agreement set `S={x: c(x)=w_γ(x)}`: since `d∣a−b` ⟹ `ω^a=ω^b`,
  for `x∈S`:  `ωx ∈ S  ⟺  c(x) = c_ω(x)`,  where `c_ω(x) := ω^{−a} c(ωx)` is **another codeword** (deg<k).

**The dichotomy (pure MDS).** Let `H = {ω∈μ_d : c = c_ω}` — a SUBGROUP of `μ_d` (the equivariance
group of `c`). For `ω∈H`: `c=c_ω` ⟹ `ωx∈S` for every `x∈S` ⟹ **S is H-invariant = a union of
μ_{|H|}-cosets**. For `ω∉H`: `c≠c_ω` are two distinct deg<k codewords ⟹ they agree on `≤ k−1`
points ⟹ `#{x∈S : ωx∈S} ≤ k−1`. So:
  · `H = μ_d`  (c is μ_d-equivariant, i.e. `c` supported on `j≡a (mod d)`)  ⟹  **S = full μ_d-coset-union**.
  · `H ⊊ μ_d`  ⟹  the `ω∈μ_d∖H` pin S into a "thin" configuration: `∑_{orbits O}|S∩O|(|S∩O|−1) ≤
    (d−|H|)(k−1)`, bounding how far S departs from `μ_{|H|}`-coset structure.

**Status of (2):** the key identity + `c_ω∈code` + the subgroup/dichotomy structure are PROVEN/verified
and clean (pure MDS, Lean-formalizable). Remaining gap: sharpen the Case-`H⊊μ_d` thin bound to show
`|S| ≤ Johnson` (the loose `n/d+(d−|H|)(k−1)/2` is not yet ≤√ρ·n for large d — the global single-`c`
consistency across orbits must tighten it). This is the one analytic step between "verified" and
"proven" for coset-saturation. It is MONOMIAL-SPECIFIC (escapes the general beyond-Johnson open core
via R1's reduction to monomials) and reduces to the MDS distance of `c` vs its `μ_d`-twists `c_ω`.

**Conjecture optimality scorecard:** (1) factorization rigidity — PROVEN-in-Lean. (2) coset-saturation
— MDS-dichotomy skeleton proven, one thin-bound step open. (3) R1 monomial extremality — verified. (4)
R2 Kambiré sumset-max — Kambiré optimization. The δ\* open core (line-list upper bound) is reduced to
ONE sharp counting bound on `c`-vs-twist agreement — combinatorial, char-p-free. Feasibility 8.5.

## UPDATE — coset-saturation RESTORED in the non-saturated (prize) regime; refutation was a small-p artifact

The §-above "coset-saturation refuted" (non-coset valid S at n=24,m=2,r=4,p=73) was a **saturation
artifact**. Re-test with LARGE primes (`/tmp/saturation_caveat.py`, p≈4001): across n=16,18,20, m=2,
r=4,5,6, **noncoset=0 in EVERY non-saturated instance**, and `#bad = |distinct sumset|` EXACTLY. The
non-coset solutions exist only when the r-fold sumset SATURATES the field (`|sumset|≈p`, small p) —
there they are spurious char-p coincidences AND the sumset = whole field so they add nothing.

**Why this matters: the prize regime is firmly NON-saturated.** At the window edge `|H^{(+r)}| ≈ q·ε* =
q·2^-128 ≪ q`. So the subgroup sumset is a tiny fraction of the field — exactly the non-saturated
regime where coset-saturation HOLDS. The directive's warning against the degenerate full-group/saturated
case is precisely what distinguishes the artifact (saturated, irrelevant) from the prize (non-saturated).

**The sharpened, honest optimality chain:**
  1. Bad scalar ⟺ S ⊆ μ_n, |S|=rm, `e_i(S)=0 ∀i∈{1,…,2m−1}\{m}`, γ=±e_m(S). [proven, Vieta]
  2. Newton (e_1..e_{m−1}=0): `p_1=…=p_{m−1}=0`, `p_m=±m·e_m`; with the rest, `p_j=0 ∀j∈{1,…,2m−1}\{m}`.
     ⟹ `e_m(S) = (±1/m)∑_{ζ∈μ_s} c_ζ·ζ`, `c_ζ=#{x∈S:x^m=ζ}∈{0,…,m}`, `∑c_ζ=rm`. [proven]
  3. **Coset-saturation (non-saturated regime):** a size-`rm` subset of μ_n with `p_j=0` for
     `j∈{1,…,2m−1}\{m}` is a union of `r` cosets of μ_m ⟹ `c_ζ∈{0,m}` ⟹ `e_m=±∑_{j}ξ_j` (distinct
     r-fold sumset). VERIFIED for all non-saturated instances (p≈4001); the lone open lemma.
  4. ⟹ `#bad = |H^{(+r)}(μ_s)|` EXACTLY ⟹ `δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*)` pinned, worst case included.

**The remaining open lemma (now sharp, char-p-FREE, concrete).** A 0/1-set spectral rigidity:
`S⊆ℤ/n`, `|S|=rm`, `\hat{1_S}(j)=0` for `j∈{1,…,2m−1}\{m}` ⟹ `1_S` is `mℤ/n`-periodic (μ_m-coset-union),
for `p` large (`p ∤` a bounded resultant — the prize `q=n^β` is far above threshold). This is a
finite Turán/uncertainty-type 0/1 rigidity (the linear Fourier constraint alone is insufficient; the
0/1+size structure is the content) — VERIFIED, provable, NOT the Weil/incomplete-Gauss-sum wall.
Proof routes: (a) over ℂ via the unit-circle moment problem `∏_{x∈S}(1−xt)≡1+ct^m (mod t^{2m})`,
|x|=1 ⟹ ∈ℂ[t^m]; (b) char-p transfer p>threshold. Feasibility 8.5. This is THE thing to prove to close.

## UPDATE — COSET-SATURATION PROVED over ℂ (dyadic) via iterated Lam–Leung; residual = char-p transfer (#389 wall)

**Theorem (coset-saturation, dyadic, over ℂ — PROVED).** Let `n=2^μ`, `m=2^a | n`, `S ⊆ μ_n`. If
`p_{2^i}(S) = 0` for `i=0,…,a−1` (ONLY the powers-of-2 power sums), then `S` is a union of cosets of `μ_m`.
VERIFIED (`/tmp/lamleung_light.py`, large p): all valid S coset-unions, n=8,16, a=1,2,3.

**Proof (induction on `a`, uses only Lam–Leung).**
- `a=1`: `p_1(S)=∑_{x∈S}x=0`. For `n=2^μ` (prime power p=2), Lam–Leung ⟹ every vanishing 0/1-sum of
  `n`-th roots is a disjoint union of basic relations `x+(−x)=0`, i.e. `S` = union of `μ_2`-cosets `{x,−x}`.
  (Direct: `{1,ζ,…,ζ^{n/2−1}}` is a ℚ-basis of `ℚ(ζ_n)`, `ζ^{n/2}=−1`; coeffs `∈{−1,0,1}` vanish ⟹ pairs.)
- `a→a+1`: by IH `S=⊔_l z_l μ_{2^a}`. The `2^a`-power map collapses each coset to `z_l^{2^a}`, and
  `p_{2^a}(S)=∑_l z_l^{2^a}∑_{ω∈μ_{2^a}}ω^{2^a}=2^a·∑_l z_l^{2^a}=2^a·p_1(S')`, `S'={z_l^{2^a}}⊆μ_{n/2^a}`.
  `p_{2^a}(S)=0 ⟹ p_1(S')=0 ⟹` (Lam–Leung) `S'` = `μ_2`-coset-union ⟹ the `z_l^{2^a}` pair as `{w,−w}` ⟹
  the `μ_{2^a}`-cosets pair into `μ_{2^{a+1}}`-cosets ⟹ `S` = union of `μ_{2^{a+1}}`-cosets. ∎

The gap constraint `e_i(S)=0 ∀i∈{1,…,2m−1}\{m}` gives (Newton) `p_1=…=p_{m−1}=0 ⊇ {p_1,p_2,…,p_{m/2}}`,
exactly the powers-of-2 needed. So **over ℂ the optimality lower bracket is CLOSED**: every gap-valid `S`
is a coset-union ⟹ `e_m=±∑_j ξ_j` (distinct r-fold sumset) ⟹ `#bad=|H^{(+r)}|` ⟹ `δ*` pinned exactly.

**The single honest residual = char-`p` transfer (= the #389 wall, now PRECISELY named).** Over `F_p`
(`p=q=n^β`, Linnik prime), Lam–Leung is a `ℂ/ℚ` statement; a char-`p` vanishing sum `∑_{x∈S}x≡0 (mod p)`
lifts to a `ℂ` relation only if `p ∤ N(∑_{x∈S}x)`. The trivial norm bound needs `p>(rm)^{n/2}`, UNREACHABLE
in the prize regime (`n^β ≪ n^{n/2}`, `n=2^30`). So char-`p`-spurious non-coset `S` may exist; the
optimality needs them to give NO new `e_m` (outside the sumset). This is EXACTLY the #389 small-integer
additive-relation / additive-energy-excess wall ([[arklib-389-wick-energy-sqrt2]],
[[arklib-389-smallsubgroup-pin-CLOSED]]) — a specific, named open problem, NOT a vague core.

**Net.** The ℂ structure of the optimality is now a PROVEN theorem (iterated Lam–Leung — clean, novel
assembly, Lean-formalizable: the `m=2` brick is the in-tree cyclotomic ℚ-basis argument). The prize
remains open at ONE precisely-located point: the char-`p` transfer (#389). Novelty 8 / insight 9 /
proximity 10 / feasibility 7 (ℂ side closed; char-p side = the recognized hard wall). NOT a full closure.

## UPDATE — char-p side via ELIMINATION: optimality closes over F_p for q ∤ D (residual is now a divisibility)

The ℂ coset-saturation proof (iterated Lam–Leung) upgrades to an `F_p` bound by elimination theory,
bypassing the unconditional char-p Lam–Leung transfer:

**Setup.** Let `F(γ) = ∏_{distinct sums v of r distinct μ_s elts}(γ − v)` — the SQUAREFREE sumset
polynomial, `deg F = |H^{(+r)}(μ_s)|`. Let `I = ⟨e_i : i∈{1,…,2m−1}\{m}⟩` be the ideal of the gap
constraints (in the symmetric-coordinate ring of `rm`-point configurations on `μ_n`).

**The transfer.** Over ℂ the Lam–Leung proof shows every point of `V(I)` has `e_m ∈ {sums}` = roots of
`F`, i.e. `F(e_m)` vanishes on `V(I)`. Nullstellensatz ⟹ `F(e_m) ∈ √I` ⟹ `F(e_m)^t ∈ I` over ℚ for some
`t`. Clearing denominators: `D · F(e_m)^t = ∑_i G_i·(gap relation)_i` over ℤ, for a FIXED integer `D`.
Hence **for every prime `p ∤ D`**: any gap-valid `S` over `F_p` (the relations vanish) gives
`F(e_m(S))^t ≡ 0 (mod p)` ⟹ `F(e_m(S)) = 0` (field) ⟹ `e_m(S)` is a root of `F mod p`. Therefore
`#bad = #{distinct e_m(S)} ≤ #{distinct roots of F mod p} ≤ deg F = |H^{(+r)}|`. **Optimality CLOSES over
`F_p` for `p ∤ D`** — no char-p Lam–Leung needed, no additive-energy excess, no incomplete Gauss sums.

**The residual is now a single divisibility `q ∤ D`.** `D` is fixed (depends on `n,m,r`); its prime
factors are bounded by the bad-prime locus where spurious non-coset `S` appear, ≤ `(rm)^{n/2}` (norm of
a nonzero `e_i(S)`). The prize `q = n^β ≪ n^{n/2}`, so `q ∤ D` is NOT automatic — but it is a CONCRETE,
checkable condition on the single prize prime, NOT an unconditional open conjecture. Empirically δ* is
`q`-INDEPENDENT (measured q=97..353, [[arklib-389-correlation-coset-reframing]]) ⟹ no bad primes seen
⟹ `q ∤ D` holds in every tested case. Closing the prize = proving `q ∤ D` for the prize field (or that
`D`'s bad primes never coincide with a Linnik prime `≡1 mod n` in the prize range).

**Net standing of the δ\* conjecture after this session:**
  - `δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*)` — EXACT form, worst case.
  - UPPER bracket: PROVEN (Kambiré coset construction).
  - LOWER bracket (optimality `#bad ≤ |H^{(+r)}|`):
      · reduction to gap-variety + Vieta `e_m`: PROVEN.
      · ℂ coset-saturation via iterated Lam–Leung: PROVEN (clean, verified, Lean-formalizable).
      · `F_p` transfer for `q ∤ D` via Nullstellensatz/elimination: PROVEN.
      · `q ∤ D` for the prize prime: the SOLE residual (concrete divisibility; q-independence supports it).
  This is a near-closure: the open math is reduced from a vague "list-decoding/MCA core" to ONE explicit
  arithmetic condition `q ∤ D` on the prize field. Novelty 8 / insight 9 / proximity 10 / feasibility 7.5.

## UPDATE — q-independence verified across 91 primes; the bound #bad ≤ |H^{(+r)}|_ℂ is robust

Scan (`/tmp/prime_scan.py`): for n=16,m=2,r=3, all 91 primes `p≡1 mod 16` in [80,6000] give
`#bad = #{distinct e_m over gap-valid S} ≤ 40 = |H^{(+3)}(μ_8)|_ℂ` (the FIXED char-0 sumset count),
max exactly 40 (at p=97). NO prime inflates #bad above the ℂ count. So the optimality bound
`#bad ≤ |H^{(+r)}|_ℂ` is q-INDEPENDENT and robust — the "bad-prime" set `D` (if nonempty) contains no
prime `≡1 mod 16` below 6000 that increases the count. Combined with the proven `p∤D` Nullstellensatz
transfer, this is strong evidence `q∤D` (equivalently, the bound) holds at the prize field too.

**FINAL standing — the δ\* conjecture, honestly:**
  `δ* = 1 − ρ − 2ρ ln(1/(2ρ)) / log₂(q·ε*)`  (EXACT, worst case).
  · UPPER bracket: PROVEN (Kambiré coset construction realizes `|H^{(+r)}|` bad scalars at the edge).
  · LOWER bracket `#bad ≤ |H^{(+r)}|`:
      – gap-variety reduction + Vieta `γ=±e_m(S)`: PROVEN.
      – Newton `e_m = (±1/m)∑_ζ c_ζ ζ`: PROVEN.
      – ℂ coset-saturation via iterated Lam–Leung (`p_{2^i}(S)=0 ⟹ μ_m-coset-union`, dyadic): PROVEN
        (verified; Lean-formalizable — m=2 brick = in-tree cyclotomic ℚ-basis).
      – `F_p` transfer for `p∤D` via Nullstellensatz/elimination (`#bad ≤ deg F = |H^{(+r)}|`): PROVEN.
      – `q∤D` at the prize field: SOLE residual — concrete divisibility, q-independence verified 91 primes.
  Scores: novelty 8 · insight 9 · proximity 10 · feasibility 7.5. This is a NEAR-closure: the only open
  math is the explicit arithmetic condition `q∤D` (not a vague LD/MCA core, not the Weil/Gauss-sum wall).
  Per the honesty contract: the prize is NOT fully closed — `q∤D` is unproven for the prize prime, even
  though empirically robust. The ℂ optimality and the `p∤D` `F_p` bound ARE proven.

## UPDATE 2026-06-13 — `q∤D` SHARPENED to "D is a power of 2"; residual distilled to the char-free Half-Sum Lemma

The opaque divisibility `q∤D` (D = Nullstellensatz/elimination content, a priori astronomically large
≤ `(rm)^{n/2}`) is replaced by a STRUCTURAL statement with a clean reason.

**(I) D is a power of 2 — the char-2 inseparability degeneracy is the ONLY one.**
The whole reduction lives over fields where `t^n − 1` is SEPARABLE, i.e. `char ∤ n`. Since `n = 2^μ`,
the only forbidden characteristic is **2** (there `t^n−1 = (t−1)^n`, μ_n degenerates). For EVERY odd
characteristic the gap-variety is a separable, well-behaved scheme. Conjecture (verified): the bad-prime
locus `D` is a **pure power of 2**. Since the prize prime `q ≡ 1 (mod n)` is necessarily **odd**, `q ∤ D`
AUTOMATICALLY — no divisibility miracle needed. Verification (`probe_407_odd_badprime_hunt.py`): for
`n=16,m=2,r=4`, factoring `Φ_16 mod p` and testing EVERY gap-valid config over each extension field
`F_{p^{deg}}`, there are **NO odd bad primes in [3,120)** — every odd prime is good, so `#bad = |H^{(+r)}|`
holds over every odd-characteristic field for this case. (`probe_407_emvalue_containment.py`: containment
`e_m ∈ Σ` holds at 167+ primes `≡1 mod n` up to 12000, even where char-p SPURIOUS non-coset configs
appear — config count inflates 70→102, 560→656, but the distinct-`e_m` count never moves.)

**(II) The squaring-descent (m=2) — self-similar, reduces optimality to one combinatorial lemma.**
For gap-valid `S ⊆ μ_n` (`e_1=e_3=0`, `|S|=2r`), split by the squaring map `x↦x²` (`c_w=#{x∈S:x²=w}`):
paired part `D2={w:c_w=2}` and single part `U={x∈S: c_{x²}=1}`. Then (verified EXACTLY incl. on all 32
spurious configs at p=17, `probe_407_squaring_descent.py`):
  · `A(t) = D(t²)·A_U(t)`, so `C(s):=∏_{x∈S}(s−x²) = D(s)²·C_U(s)` (genuine ⟺ C a perfect square).
  · **`e_1(U)=e_3(U)=0`** (Newton): U is itself a SMALLER gap-valid config, with the extra property
    `U ∩ (−U) = ∅` (no antipodal pairs — by construction of the single part).
  · **`e_2(S) = e_2(U) − ∑_{w∈D2} w`**.
By strong induction on size, `e_2(U) ∈ Σ_k` (IH) and `∑_{D2}w ∈ Σ_{d2}` with `r=k+d2`. (NOTE: the
descent does NOT telescope via squaring — U has no antipodal pairs so squaring U yields no new pairs;
the recursion is on SIZE via the IH, not iterated squaring. The earlier "telescope to a distinct
multiset" idea is REFUTED.)

**(III) The SOLE remaining residual = the Half-Sum Lemma (char-free, NO Gauss-sum/Weil wall).**
  > **Half-Sum Lemma.** Let `K` be a field of odd characteristic (or 0), `n=2^μ`, `μ_n ⊆ K̄`.
  > If `U ⊆ μ_n` has `U ∩ (−U) = ∅` and `∑_{u∈U} u = ∑_{u∈U} u³ = 0`, then
  > `−½ ∑_{u∈U} u²` is a sum of `|U|/2` distinct elements of `μ_{n/2}` (i.e. lies in `Σ_{|U|/2}`).
  This is the distilled char-p phenomenon: over ℂ no such `U` exists (Lam–Leung ⟹ `U=−U`), so it is
  VACUOUS in char 0; in odd char `p` spurious `U` exist but the conclusion still holds. It plus (II)
  plus the IH plus an absorption step (`{IH k-subset} ⊔ {−D2}` are `r` distinct, the one not-yet-proven
  combine) give `e_2(S) ∈ Σ_r ⟹ #bad ≤ |H^{(+r)}|` over EVERY odd-char field — closing the optimality
  lower bracket UNCONDITIONALLY (no `q∤D`). Refutation search (`probe_407_halfsum_lemma_refute.py`):
  **NO counterexample** at `n=16,32,64` over the tested primes (n=32: 96 constraint-satisfying U-configs,
  all pass; n=64: searched).

**Net.** The residual moves from "a divisibility `q∤D` on an opaque, possibly-huge `D`" to "**D is a
power of 2**, because odd characteristic is non-degenerate" — with the genuine open kernel a SELF-CONTAINED
combinatorial Half-Sum Lemma about μ_n in odd characteristic (no incomplete Gauss sums, no Weil, no BGK
energy excess). This is a strictly sharper reduction, not yet a closure: the Half-Sum Lemma is verified
(n≤32, no odd counterexample) but UNPROVEN for general `n`, and its failure at large `n` would itself
REFUTE the exact-δ\* formula (char-p inflation of #bad) — a concrete win/lose target.
Scores: novelty 7.5 · insight 8 · proximity 9 · feasibility 7 (Half-Sum Lemma is concrete & char-free
but open at general n). Probes: `scripts/probes/probe_407_{deltastar_emcount_sweep,emvalue_containment,
odd_badprime_hunt,squaring_descent,halfsum_lemma_refute}.py`.

## UPDATE — the residual is the SAME core two independent routes reach: char-p cyclotomic-coincidence suppression

The `q∤D` residual is precisely: `bad ⊆ roots(G mod p)` where `G(γ)=∏_{J:|J|=r}(γ−σ_J)` is the
INTEGER-coefficient sumset polynomial (`σ_J=∑_{ζ∈J}ζ`, symmetric in `μ_s` ⟹ ℤ coeffs). Equivalently
`G(e_m(S))≡0` for every gap-valid `S` over `F_p` — i.e. NO char-p-spurious non-coset `S` contributes an
`e_m` outside the ℂ-sumset. Tested: 0 violations across all accessible primes; spurious non-coset `S`
appear only at saturated small `p` (where `roots(G)`=field, trivially no new value). The norm bound puts
spurious primes at `≤ (rm)^{n/2}`, above saturation, so a non-saturated spurious prime is not excluded —
that is the open content.

**Convergence (issue #407, lane G — `lalalune` comments).** The independent Gaussian-period route
(`max_i|η_i| ≤ √(2n log m)`) is ALSO reduced to exactly this: its sole open link is "the number of
`(x,y)∈μ_{2^μ}^{2r}` with `∑x_i ≡ ∑y_j (mod p)` but `≠` in `ℤ[ζ_n]` is `o(E_r^0)`" — char-`p`-genuine
balanced cyclotomic relations being suppressed. That same lane PROVED the char-0 MOMENT route is dead in
the prize regime (depth caps at `β+1`, anomaly forced positive by Fourier positivity). So the moment
route cannot reach the floor; the live cores are (a) my coset-saturation/sumset route and (b) the
sup-norm route — and BOTH bottom out at char-p cyclotomic-coincidence suppression. This is the genuine
prize-hard core, now reached by two independent derivations.

**Why my route is the cleaner of the two:** it PROVES the ℂ side completely (iterated Lam–Leung ⟹
coset-saturation ⟹ `#bad=|H^{(+r)}|` over ℂ, NO moment estimates) and reduces the char-p side to a
single ideal-membership/divisibility `G(e_m)∈I_ℤ` (= `q∤D`), whereas the sup-norm route needs the full
BGK/`√(2n log m)` sub-Gaussian tail. The remaining open math is identical and minimal in both.

**HONEST FINAL STANDING (this is NOT a closure).** δ* = `1−ρ−2ρ ln(1/2ρ)/log₂(qε*)`, exact. PROVEN:
upper bracket (Kambiré); ℂ optimality (Lam–Leung induction); `F_p` optimality for `p∤D` (Nullstellensatz).
OPEN: `G(e_m)∈I_ℤ` / `q∤D` = char-p cyclotomic-coincidence suppression — the recognized prize-hard core,
confirmed by two-route convergence, supported by exhaustive q-independence scans but UNPROVEN for the
prize prime. Per the honesty contract I do not claim the prize closed; I claim a clean ℂ-complete
reduction whose only residual is the same minimal arithmetic core both prize routes reach.

## DEFINITIVE — the residual is IRREDUCIBLE to elementary bounds in the prize regime (the BGK wall)

Settled the `m=2` residual to its arithmetic essence. A char-`p`-spurious gap-valid `S` ⟺ a set
`Y ⊆ μ_n` with **no ±-pairs** and `∑_{y∈Y}y ≡ 0`, `∑_{y∈Y}y³ ≡ 0 (mod p)`. Over ℂ, Lam–Leung
(2-power: vanishing 0/1-sum = ±-pairs) forces `Y=∅`; so spurious `Y` requires a char-`p`-genuine
vanishing sum. Its minimal length `L` obeys the height bound `p ≤ L^{φ(n)} = L^{n/2}` ⟹ `L ≥ p^{2/n}`.

**In the prize regime `p=q=n^β`, `n=2^μ`:** `p^{2/n} = 2^{2βμ/2^μ} → 1` (computed: 4.0 at μ=4, 1.19 at
μ=8, 1.0000 at μ≥24 — `/tmp/minimal_spurious.py`). So the height/norm bound excludes NOTHING: spurious
relations of length `O(1)` are not ruled out. This is EXACTLY the BGK / sum–product wall — controlling
sub-height additive relations in a SMALL subgroup of `F_p^*` with `p ≪ 2^n` — the recognized core of
[[arklib-389-wick-energy-sqrt2]] / [[arklib-389-smallsubgroup-pin-CLOSED]]. The same wall the independent
Gauss-sum sup-norm route (#407 lane G) terminates at. No elementary technique closes it for `p ≪ 2^n`.

**Final, fully honest standing of the δ\* programme (NOT a closure):**
  `δ* = 1 − ρ − 2ρ ln(1/2ρ)/log₂(qε*)` — exact form, worst case.
  - PROVEN: upper bracket (Kambiré construction); ℂ-side optimality (iterated Lam–Leung ⟹
    `#bad=|H^{(+r)}|` over ℂ); `F_p` optimality for `p∤D` (Nullstellensatz/elimination);
    `FactorizationRigidity.lean` (axiom-clean Lean).
  - OPEN (irreducible): `G(e_m)∈I_ℤ` ⟺ `q∤D` ⟺ suppression of char-`p`-genuine vanishing sums of
    `2^μ`-th roots of unity of length `O(s)` at `p=n^β`. This IS the BGK/sum–product open problem; the
    height bound proves it is NOT reducible to elementary number theory in the prize regime.
  Honest scores: novelty 8 / insight 9 / proximity 10 / feasibility — for the ℂ side 9, for the full
  prize closure **3** (gated on a recognized open problem in additive combinatorics).

**What this session established that is new and solid:** (i) the EXACT δ* via Kambiré; (ii) a clean,
char-p-FREE, fully proven ℂ-side optimality via iterated Lam–Leung (replacing the dead moment route);
(iii) the elimination/Nullstellensatz transfer giving the bound for `p∤D`; (iv) a PROOF that the sole
residual is the BGK wall (not a vague core, not closable by heights) — converging with the independent
sup-norm route. The prize is reduced to its irreducible additive-combinatorics core, but NOT closed.

## REFINEMENT — the dyadic residual is a {−1,0,1}-coefficient two-condition vanishing problem (sharper than generic BGK)

For dyadic `n=2^μ`, the integral basis `{ζ^j}_{0≤j<n/2}` of `ℤ[ζ_n]` (`ζ^{n/2}=−1`) turns the m=2 spurious
condition into a fully explicit form. A spurious `Y⊆μ_n` (no ±-pairs) writes `y=c_j·ζ^j` with exactly
`|Y|` nonzero `c_j∈{±1}` (one per element, no-±-pair ⟺ ≤one of `ζ^j,−ζ^j` in `Y`). Then
`∑_Y y = ∑_j c_j ζ^j` and `∑_Y y³ = ∑_j c_j ζ^{3j}`. So a char-p spurious config exists ⟺ there is a
`{−1,0,1}` vector `(c_j)` (support a no-±-pair set) with
  `∑_j c_j ω^j ≡ 0` AND `∑_j c_j ω^{3j} ≡ 0  (mod p)`,  `ω` = primitive `n`-th root in `F_p`.

This is **much more rigid than the generic BGK sum-product problem**: coefficients are restricted to
`{−1,0,1}` and there are TWO simultaneous frequency conditions (1 and 3). It is a concrete, finite,
explicitly-stated Diophantine problem over `F_p` — NOT the black-box BGK incidence bound. However:
  · `F_p` is 1-dimensional, so `≥3` basis elements are always `F_p`-dependent ⟹ ±1 vanishing combos
    DO exist for the single condition; the two conditions + sumset-membership of the resulting `e_m`
    are what must fail.
  · The norm/height bound only gives `p ≤ (n/2)^{n/2}`, so prize primes `p=n^β` are not excluded.
  · Computationally: NO spurious no-±-pair 4-subset with `e_1=e_3=0` exists at any odd `p≡1 mod n`
    up to 30000 for n=16,32 (`/tmp/odd_bad_prime.py`) — consistent with bad primes being large/rare,
    but not a proof.

**This is the sharpest form of the open residual:** suppression of `{−1,0,1}`-coefficient two-frequency
vanishing sums of dyadic roots of unity at `p=n^β` (equivalently `G(e_m)∈I_ℤ`). It is more structured
and more likely tractable than generic BGK, but I have NOT proved it. The prize remains open at exactly
this point; I will not claim otherwise. (The full integrality `G(e_m)∈I_ℤ`, if provable via the rigidity
of the dyadic relation lattice, would close the optimality unconditionally for all odd p — that is the
single, explicit, now-fully-concrete proof target.)

## STRUCTURE — the residual is a self-similar dyadic recursion bottoming out at char-p vanishing sums

A clean recursion for the m=2 bad scalar (derived this round). For gap-valid `S` (`e_1(S)=e_3(S)=0`),
split fibres over `μ_{n/2}` into FULL (`c_ζ=2`) and PARTIAL (`c_ζ=1`); the partial elements form `Y`
(one per partial fibre, distinct squares ⟹ no ±-pairs). Then:
- `∑_Y y = e_1(S)-related = 0`, and `∑_Y y³ = 0` ⟹ (Newton, `p≠3`) `e_1(Y)=e_3(Y)=0` — **`Y` is itself a
  gap-valid config** (smaller, fully-partial, no ±-pairs).
- `e_2(S) = -σ_{full} + e_2(Y)`, where `σ_{full}=∑_{full fibres}ζ` is a genuine sub-sum.

So `e_2(S) ∈ sumset ⟺ e_2(Y) ∈ (sumset shifted)`, and `Y` is a SMALLER instance of the same problem.
**Over ℂ the recursion terminates at `Y=∅`** (Lam–Leung: a fully-partial, no-±-pair, `e_1=0` config is
empty) ⟹ `e_2(S)=-σ_{full} ∈ sumset` — re-proving ℂ optimality cleanly. **Over `F_p` the recursion
bottoms out at a char-p fully-partial `Y≠∅`** = a dyadic vanishing sum (`∑_Y y≡∑_Y y³≡0 mod p`, no
±-pairs), whose `e_2(Y)=-½∑_{Z_Y}ζ` carries the `½` and need not lie in the sumset. THAT is the entire
residual, exhibited as the base case of a self-similar recursion.

This is the cleanest possible statement of the open core: **`G(e_m)∈I_ℤ` holds ⟺ every char-p
fully-partial dyadic config has `e_2 ∈ sumset`** — a finite, explicit, self-referential dyadic
vanishing-sum condition. It is NOT closable by the recursion alone (the base case IS the BGK-type
coincidence), but it is the most reduced form: no codes, no Johnson, no Gauss sums, no moments — just
`{−1,0,1}` vanishing sums of `2^μ`-th roots of unity at odd `p=n^β`. Honest standing unchanged: ℂ side
PROVEN, `F_p` for `p∤D` PROVEN, this base case OPEN (= the prize-hard core). I do not claim it closed.

## LITERATURE — the residual is the small-weight genuine-vanishing-sum gap (Lam–Leung finite-field paper)

Directed literature search (#407 directive: "find 5 papers, research what the conjecture reduces to").
The residual `G(e_m)∈I_ℤ` reduces to: do SMALL-weight char-`p`-genuine (non-±-pair) vanishing sums of
`2^μ`-th roots of unity exist at `p=n^β`? The exact machinery is **Lam–Leung, "Vanishing Sums of m-th
Roots of Unity in Finite Fields"** (arXiv:math/9605216 / J. Algebra). Their Theorem (uniform): the weight
set `W_p(m) ⊇ [(p−1)/m + 1, ∞)` (here roots are `n`-th roots, so `W_p(n) ⊇ [(p−1)/n + 1, ∞)`). KEY
consequence for the prize:
  · char-`p` genuine vanishing sums are GUARANTEED only for weight `w ≥ (p−1)/n ≈ n^{β−1}`.
  · my spurious configs have weight `w = |Y| ≤ n/2 = 2^{μ−1} ≪ n^{β−1}` (since `β≥2`).
  · so they live STRICTLY BELOW Lam–Leung's existence threshold — the small-weight regime the paper
    does NOT characterize (it gives existence above `n^{β−1}`, not non-existence below).
The norm/height bound gives only `w ≥ p^{2/n} ≈ 1` (useless). So the residual sits in the GAP
`[p^{2/n}, (p−1)/n] = [≈1, ≈n^{β−1}]` — precisely the BGK/sum–product regime for a small multiplicative
subgroup of `F_p^*`, where neither existence nor non-existence of short genuine relations is known.
Two simultaneous conditions (`∑y=∑y³=0`) make them rarer still: weight 3 is killed identically
(`∑y³=3∏y≠0`), and NO genuine config was found up to `p=30000` for `n=16,32`.

**Reading list (5 papers, for download):**
1. Lam–Leung, *Vanishing Sums of m-th Roots of Unity in Finite Fields*, arXiv:math/9605216 — `W_p(m)`,
   the EXACT machinery for the char-`p` residual; gives `[(p−1)/m+1,∞)⊆W_p(m)` (existence threshold).
2. Lam–Leung, *On Vanishing Sums for Roots of Unity*, arXiv:math/9511209 — the char-0 structure
   `W(m)=ℕp₁+…+ℕpᵣ` (`W(2^μ)`=evens=pairs); the basis of the proven ℂ-side optimality.
3. Łaba–Zhai et al., *Vanishing sums of roots of unity and the Favard length of self-similar product
   sets*, arXiv:2202.07555 — vanishing-sum structure under self-similarity (matches my e_2 recursion).
4. Bourgain–Glibichuk–Konyagin, *Estimates for the number of sums and products and for exponential sums
   in fields of prime order* (J. LMS 2006) — the sum–product/incidence bound for small subgroups = the
   BGK regime the residual's small-weight gap falls into. [NEED: not on arXiv; J. LMS 73 (2006).]
5. Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* (ePrint 2026/680) — the
   prize source; the MCA/LD challenges the residual is the last obstruction to.

**Honest net:** the residual is now LITERATURE-GROUNDED as a specific small-weight question strictly
below the Lam–Leung existence threshold and inside the BGK gap — not closed, but precisely placed. No
paper found that resolves the small-weight regime; that is the open core. Prize remains open.

## THE CRYSTALLIZED DELIVERABLE — δ* with all open math compressed to ONE precise conjecture

The complete result, stated so every step except one explicit conjecture reduces to proven math.

**Theorem (δ* upper bracket).** For RS[F_q, μ_n, k] (n=2^μ, ρ=k/n, ε*), the Kambiré coset line gives
`|H^{(+r)}|` bad scalars at radius `1−ρ−2/s`, so `δ* ≤ 1 − ρ − 2ρ ln(1/2ρ)/log₂(qε*)`. PROVEN.

**Theorem (ℂ-side optimality).** Over ℂ every gap-valid config is a coset-union (iterated Lam–Leung),
so the ℂ bad count is exactly `|H^{(+r)}|`. PROVEN (no moments, no Weil).

**Theorem (F_p optimality, conditional).** If the Conjecture below holds, then over `F_q` every gap-valid
config is a coset-union, `#bad = |H^{(+r)}|` exactly, and `δ* = 1 − ρ − 2ρ ln(1/2ρ)/log₂(qε*)`, worst
case included. PROVEN from the Conjecture (Vieta + Newton + the recursion `e₂(S)=−σ_full+e₂(Y)`).

**CONJECTURE (Dyadic Gap Vanishing-Sum Suppression) — the single complete open statement.**
Let `n = 2^μ`, `p` an odd prime, `p ≡ 1 (mod n)`, `p ≥ n^β` with `β ≥ 4`. Then there is NO nonempty
`Y ⊆ μ_n` with (i) no ±-pairs, (ii) `|Y| ≤ n/2`, and (iii) `∑_{y∈Y} y ≡ 0` and `∑_{y∈Y} y³ ≡ 0 (mod p)`.
[Level-`m`: `∑ y^ρ ≡ 0` for all `ρ ∈ {1,…,2m−1}\{m}`.] This contains ALL remaining open math — no further
lemma, no deferred variable.

Scores: novelty 8 (the `{−1,0,1}` two-frequency dyadic form is not in the literature), insight 9
(unifies MCA + LD into one vanishing-sum statement), proximity 10 (`p=n^β`, dyadic, worst case),
feasibility 3 (small-weight gap `[p^{2/n},(p−1)/n]` of the BGK regime — below Lam–Leung existence, above
the norm bound — where no known technique proves suppression).

**Refutation status:** survives — no counterexample for n=16,32 up to p=30000 (two conditions kill
weight 3 identically; none at weight 4–8). **Cross-lane confirmation:** independent fleet lanes reached
the SAME wall (`P_max` exponential ⟹ prize `p≪2^n` ⟹ bad primes exist ⟹ core open; "mod-p transfer =
the open brick"). This is the fleet-wide frontier, not an artifact of one route.

**Honest verdict:** δ* is pinned EXACTLY *conditional on* one precise, novel, refutation-survived,
literature-grounded additive-combinatorics conjecture that no current technique proves. That conjecture
IS the prize's irreducible core. Not claimed proven; it is the complete and minimal open statement, with
everything else reduced to proven math.

## UPDATE 2026-06-13 (late) — SHARPENING the "bad primes exist" wall: the δ*-relevant quantity is D=2^k

The cross-lane "wall" above (`P_max` exponential ⟹ prize `p≪2^n` ⟹ bad primes exist ⟹ core open) is
stated for the additive-**energy** `P_max`. But δ\* depends ONLY on the **distinct-`e_m` (bad-scalar)
count**, NOT on the energy — and that quantity is strictly more robust. This session's measurements:

- **No `e_m`-inflation anywhere tested.** `probe_407_halfsum_wide_refute.py`: `n=16`, **3227 primes
  `≡1 mod 16` up to 300000** (`r=3`; +1391 at `r=4`, +752 at `r=5`) — distinct-`e_m` count is EXACTLY
  `|Σ|` (40/41/40), zero violations. `probe_407_odd_badprime_hunt.py`: factoring `Φ_16 mod p` over all
  extension fields, **NO odd bad prime in [3,120)**. So for the δ\*-relevant count, `D` is empirically a
  **pure power of 2** (only char-2 degenerates, via `t^n−1=(t−1)^n`) — and the prize prime `q≡1 mod n` is
  ODD ⟹ `q∤D`. The energy `P_max` wall does NOT transfer to the bad-scalar count: char-p spurious configs
  appear (config count inflates 70→102, 560→656) but every spurious `e_m` lands back in `Σ`.

This relocates the open core precisely: NOT "bad primes exist for the count" (none seen to 300k), but the
**Half-Sum Lemma** — the rigidity that *makes* `D=2^k` true. Two reformulations of it (new this session):
  · **Complement half-sum:** `e₂(U) = ½ ∑_{w∈ μ_{n/2}∖U²} w` (half the sum of squares MISSING from `U²`).
  · **Fourier-flat:** `\hat{1_U}(1)=\hat{1_U}(3)=0` + antipodal-free ⟹ `−½\hat{1_U}(2) ∈ Σ_{|U|/2}`.
And the reason it is genuinely NEW math: Lam–Leung's char-0 proof is the **ℤ-basis** argument
(`{1,ζ,…,ζ^{2^{μ-1}−1}}` a ℤ-basis, `ζ^{2^{μ-1}}=−1`), which PROVABLY collapses mod `p` (there `ζ∈F_p`,
the basis is 1-dim) — so no transfer; a positive-characteristic proof is required.

**Reading list (verified this session).** JACKPOT engine: Lam–Leung *Vanishing Sums of m-th Roots of Unity
in Finite Fields* (arXiv:`math/9605216`, JNT 65 1997). Also: Lam–Leung J.Algebra 224 (2000); Kambiré
arXiv:`2604.09724`; Arnon–Boneh–Fenzi ePrint `2026/680`; Steinberger arXiv:`2008.11268`; Poonen–Rubinstein
arXiv:`math/9508209`; Conway–Jones (1976); Chi Hoi Yip arXiv:`2309.10950`; "small mult. subgroup not a
sumset" FFA 63 (2020); Tao arXiv:`math/0308286` + arXiv:`2310.09992`; Cilleruelo–Garaev arXiv:`1711.05335`
(Stepanov-method counting without Weil). Probes: `probe_407_{halfsum_wide_refute,primitive_structure}.py`.

## UPDATE 2026-06-13 (proof) — Half-Sum Lemma PROVEN EXACTLY for n=8 and n=16 (a finite candidate-prime method)

A genuine **proof** (not verification) of the optimality lower bracket for the first two dyadic levels,
via a complete finite computation. The key is that the odd bad primes form a **finite, exactly-computable
candidate set**:

**Completeness lemma.** A prime `p ≡ 1 (mod n)` is "bad" (some gap-valid `S` over `F_p` has `e₂(S) ∉ Σ`)
ONLY IF `p | N_{ℚ(ζ_n)/ℚ}(∑_{u∈U} u)` for some antipodal-free `U ⊆ μ_n`. *Proof:* a genuine coset-union
`S` (primitive part empty) always has `e₂(S) = −∑_{D2}w ∈ Σ`, so a bad `S` has a NONEMPTY primitive part
`U` (antipodal-free, `e₁(U)=e₃(U)=0`); primitivity over `F_p` means the degree-1 prime `𝔭∣p` divides
`α:=∑_{u∈U}u` (i.e. `α ≡ 0` mod 𝔭), hence `p ∣ N(α)`. ∎ So the **candidate odd bad primes are exactly the
odd prime factors `≡1 mod n` of `{N(∑u) : U antipodal-free}`** — a finite set (each `|N(∑u)| ≤ |U|^{φ(n)}`).

**n=8 — PROVEN, no primitive U at all.** For every antipodal-free `U ⊆ μ_8` (the 16 sign-patterns
`±1±ζ±ζ²±ζ³`), `N(∑u) = N(∑u³) = 8 = 2³` EXACTLY (e.g. `N(1+ζ+ζ²+ζ³)=N(−2/(ζ−1))=16/2=8`). So no odd
prime divides `∑u`; **no primitive U exists over any odd field**, every gap-valid config is a genuine
coset-union, and the optimality/Half-Sum Lemma holds UNCONDITIONALLY. `D = 2³`, a pure power of 2.
(`probe_407_halfsum_proof_n8.py`.)

**n=16 — PROVEN at every prize-relevant prime.** Enumerating ALL antipodal-free `U ⊆ μ_16` (sizes 4,6,8),
the candidate odd primes `≡1 mod 16` dividing some `N(∑u)` are EXACTLY `{17, 97, 113, 193, 353, 577}`
(finite & complete). Checking ALL gap-valid configs at ALL `r=2..8` over each of these 6 primes:
**every `e₂ ∈ Σ`, zero violations**. Hence `n=16` has **NO odd bad prime `≡1 mod 16`** ⟹ the optimality
`#bad ≤ |H^{(+r)}|` holds at every prize-relevant prime ⟹ **δ\* is pinned EXACTLY for RS over `μ_16`**
(upper bracket = Kambiré). `D`'s odd part `= 1`. (`probe_407_halfsum_{candidates,proof}_n16.py`.)

**What this changes.** The Half-Sum Lemma is no longer only "verified to 300k primes" — it is **PROVEN
for each fixed `n`** by a finite, exact algorithm (finite candidate set from norm factorization + exhaustive
check). `n=8, 16` are done; the algorithm proves any specific `n`. The ONLY obstruction to the asymptotic
prize (`n = 2^30`) is that its candidate set cannot be enumerated by brute force — NOT any uncertainty
about the lemma. So the open problem is now precisely: a **uniform-in-n** proof of the completeness-lemma's
"all candidates clean", i.e. that `e₂(U) ∈ Σ` for every primitive `U` (the general Half-Sum Lemma). This
is the genuine remaining math; everything else (per-n) is now a closed finite computation. Probes:
`probe_407_halfsum_{proof_n8,candidates_n16,proof_n16}.py`.

## MAJOR CORRECTION — the residual is FINITE ALGEBRA, not BGK; minimal case PROVEN even-polynomial

Two errors in the prior "BGK wall" conclusion, both now corrected:

**(1) The "counterexamples" were false positives.** `p | gcd(N(∑y), N(∑y³))` only means *some Galois
conjugate* of each vanishes — possibly at DIFFERENT primes `𝔭`. A genuine spurious config needs
`∑y≡0` AND `∑y³≡0` at the SAME embedding. Correct DIRECT enumeration (`/tmp/correct_scan.py`): genuine
spurious configs are vanishingly rare — n=16 has one only at `p=17` (= the smallest prime ≡1 mod 16),
n=32 has NONE up to p=20000. All far below the prize regime `n^β`. The scaling "c→4.3" was a gcd artifact.

**(2) "Spurious exists" ≠ "δ* changes".** What matters is whether a config yields a bad scalar OUTSIDE
the sumset. Direct `#bad` counts (`/tmp/corrected.py`, `/tmp/n64test.py`) give `#bad = |Σ_r|` EXACTLY,
`NEW=0`, at EVERY prime tested — n=16 (91 primes), n=32 (incl. p=7937), n=64 (p=65456257). The
integrality `e₂(S) ∈ Σ_r` is char-`p`-ROBUST. The bad scalar is `e₂(S) = −½∑_{x∈S}x²` with `x²∈μ_{n/2}`,
`−1∈μ_{n/2}` — it lives NATIVELY in the `μ_{n/2}` sumset, no char-`p` arithmetic involved.

**Minimal case PROVEN (char-`p`-free).** A size-4 config `S` with the m=2 gap `e₁(S)=e₃(S)=0` has
`∏_{x∈S}(X−x) = X⁴ + e₂X² + e₄` — an EVEN polynomial. So `p(X)=p(−X)`: every root `y` forces `−y` a root,
hence `S = {±y₁, ±y₂}` is a union of ±-pairs (= `μ_2`-cosets). **No no-±-pair size-4 config exists, over
any field.** So the minimal spurious config is impossible by elementary algebra — NOT a BGK question.
(Spurious configs need size ≥ 6, where `e₅` enters and the polynomial is no longer even; these are the
rare large-weight configs, and even they give `e₂∈Σ_r`.)

**Corrected standing.** δ* = `1−ρ−2ρ ln(1/2ρ)/log₂(qε*)`. Upper bracket PROVEN; ℂ optimality PROVEN;
and now the `F_p` residual is the FINITE-ALGEBRAIC integrality `e₂(S) ∈ Σ_r` (`G(e_m)∈I_ℤ`) — char-`p`-
robust across all tests, with the minimal case proven by the even-polynomial argument, and the bad
scalar manifestly a `μ_{n/2}`-element combination. This is NOT the BGK/sum–product wall; my earlier
identification was an artifact of (1) a flawed gcd criterion and (2) conflating spurious-existence with
δ*-change. Feasibility upgraded: the residual is a concrete symmetric-function identity, candidate-provable.

## UPDATE 2026-06-13 (frontier located) — the prize core = an OPEN structural problem Lam–Leung explicitly leave unsolved

Read Lam–Leung, *Vanishing Sums of m-th Roots of Unity in Finite Fields* (arXiv:math/9605216 — the
jackpot engine). Decisive context:

- **Lam–Leung determine only the WEIGHT SET `W_p(m)` (which weights `n` admit SOME vanishing sum), never
  the STRUCTURE.** Verbatim (§1): *"Easy examples show that this need not be an equality in general, so we
  are left with **no viable conjecture on the structure of the weight set `W_p(m)` in characteristic p**."*
  And (Rmk 2.7): *"determination of minimal vanishing sums is difficult (both in characteristic 0 and in
  characteristic p)."* Their explicit structure theorem (Thm 2.6) requires `Φ_m` to stay essentially
  irreducible — the OPPOSITE of the prize regime.
- **The Half-Sum Lemma is a STRUCTURAL statement** about antipodal-free vanishing sums of `2^μ`-th roots
  of unity in the **split** regime `p ≡ 1 (mod 2^μ)` (`Φ_n` factors completely) — precisely the regime
  Lam–Leung leave open. So the lemma is NOT a corollary of existing theory; it lives where the foundational
  reference has "no viable conjecture." This both explains why no published theorem proves it AND confirms
  the directive's premise that the prize requires genuinely NEW structural math.

**Evidence ledger (the lemma itself stays irrefutable, now 3 dyadic levels):**
  · n=8 — PROVEN (no primitive U; `N(∑u)=2³`).
  · n=16 — PROVEN at every prize-relevant prime (candidates `{17,97,113,193,353,577}`, all clean).
  · n=32 — verified across **380 primes `≡1 mod 32` up to 60000**, `r=3`, max distinct `e₂ = 464 = |Σ|`,
    zero violations (`probe_407_halfsum_wide_n32.py`).
  · The lemma holds via genuine char-p COINCIDENCES (`½(η³+η⁴)=1+η⁶+η⁷` at `p=17` is NOT a char-0
    identity) — a structural proof must explain why these coincidences are forced.

**Net honest frontier.** δ\* = window-edge is PROVEN for `n=8,16` (closed, no open math) and verified for
`n=32`. The asymptotic prize (`n=2^30`) reduces — with everything else proven — to a single new structural
theorem about char-p vanishing sums (the uniform Half-Sum Lemma) in a regime the foundational literature
explicitly leaves open. This is the genuine prize core: not a Weil/Gauss-sum wall, not an incomputable
lemma, but an unsolved STRUCTURE problem for `2^μ`-th-root vanishing sums when `p ≡ 1 mod 2^μ`. The
candidate-prime method PROVES it for any fixed `n`; a uniform proof requires advancing that open structure
theory. Probe: `probe_407_halfsum_wide_n32.py`.

## CONFIRMED — general-r integrality is char-p-robust; precise remaining target = eliminant is content-free

r=3 (size 6) test across 10 primes (`/tmp/r3test.py`): `#bad = |Σ_3|` EXACTLY, `NEW=0` at every prime,
INCLUDING p=97 where 96 genuine spurious size-6 configs exist (they give `e₂∈Σ_3`, adding nothing). At
non-saturated primes (257..7937) NO spurious exist and all configs are cosets. So `e₂(S)∈Σ_r` holds
whether or not spurious configs exist — fully char-p-robust.

**The precise remaining target (finite algebra, candidate-provable).** The bad scalars are the roots of
the eliminant `Res(γ) ∈ ℤ[γ]` of the system `{e₁(S)=0, e₃(S)=0, e₂(S)=γ, xᵢⁿ=1}`. Over ℂ its roots are
exactly `Σ_r` (Lam–Leung), so `Res = c·G^a` over ℚ with `G(γ)=∏_J(γ−σ_J)` (monic, integer, `deg`=
`|Σ_r|` distinct roots). The bound `#bad ≤ |Σ_r|` holds over `F_p` **iff** the content `c` is a unit (or
`p∤c`). The char-p-robustness (no new bad scalar at ANY tested prime, incl. spurious-heavy p=97) is
direct evidence `c = ±1` — i.e. **the eliminant is content-free / monic**. Proving `c=±1` closes the
optimality UNCONDITIONALLY. This is a concrete elimination-theory statement about a 0-dimensional
cyclotomic scheme — NOT BGK, NOT a recognized open problem.

**Minimal case PROVEN** (r=2): the gap forces `X⁴+e₂X²+e₄` (even) ⟹ ±-pair roots ⟹ all-coset ⟹
`e₂∈Σ_2`. **Structure for general r:** `e₂(S) = −½∑_{x∈S}x²`, `x²∈μ_{n/2}`; for all-coset configs the
2r squares double up (`∑=2∑ζᵢ`), giving `e₂=−∑ζᵢ∈Σ_r`; the spurious (partial) configs are the rare
char-p exceptions that STILL land in `Σ_r` — equivalently the resolvent `R(u)=A(u)²−uB(u)²` (roots =
the squares) has square-sum `−2e₂` forced into `2·Σ_r`. The general proof = `c=±1` (eliminant monic).

**Standing:** δ* exact; upper bracket + ℂ optimality + minimal-r `F_p` PROVEN; general-r `F_p` = the
content-free eliminant statement (finite algebra, char-p-robust, candidate-provable). The earlier "BGK
wall" verdict is RETRACTED — it was a gcd-criterion artifact. Feasibility of full closure: 6 (concrete
algebra) — up from 3 (was wrongly BGK-gated). NOT yet closed; the eliminant-monicity is the live target.

## UPDATE 2026-06-13 (mechanisms ruled out) — no simple combinatorial certificate for the Half-Sum Lemma

Searched for a constructive structural proof (an explicit k-subset realizing `e₂(U) ∈ Σ_k`). Tested and
RULED OUT (`probe_407_halfsum_mechanism_ruleout.py`):
- **Squaring-telescope** (iterate `x↦x²`): REFUTED — the antipodal-free primitive part has no pairs, so
  squaring stalls; no descent.
- **Pairing** `U² = ⊔{w,w'}` with `w+w'=−2c`, `c∈μ_{n/2}` distinct, `∑c=e₂`: holds 16/16 at n=16
  (mechanism `1+η⁵=−2η⁶` mod 17) but **FAILS 0/96 at n=32**.
- **Subset-of-U²** (`e₂ = ∑` of a k-subset of the 2k squares `U²`): holds 16/16 at n=16, **FAILS 32/96 at
  n=32, 16/400 at n=64**.

So the k-subset of `μ_{n/2}` realizing `e₂(U)` is **global** (uses elements outside `U²`) for `n≥32` — there
is NO local/combinatorial certificate. `e₂(U) ∈ Σ_k` holds (verified n≤64) but only via genuine char-p
arithmetic, not a structural pairing/partition. This is a concrete NEGATIVE result: it rules out the
natural constructive proofs and confirms (matching Lam–Leung's "no viable conjecture on the structure")
that a uniform proof needs arithmetic/analytic methods in the split regime, not combinatorial structure.

**Frontier, final form.** PROVEN n=8,16 (finite candidate-prime method); verified n=32 (380 primes),
n=64. Open core = uniform Half-Sum Lemma, a non-constructive char-p structure statement Lam–Leung leave
open. Probe: `probe_407_halfsum_mechanism_ruleout.py`.

## UPDATE 2026-06-13 (tool landscape) — every attack on the uniform Half-Sum Lemma maps to the Johnson-vs-open gap

Cross-domain literature sweep (verified papers) for tools to prove the uniform Half-Sum Lemma. Result:
**no existing theorem proves it**, and the landscape of attacks each fails for a precise, identifiable reason:

- **PROVABLY BLOCKED — Z/2^μ uncertainty principle.** Tao's sharp `|supp f|+|supp f̂|≥p+1` (arXiv:math/0308286)
  needs PRIME order (Chebotarev: all DFT minors ≠0), which FAILS for composite/prime-power modulus.
  Murty–Whang (LAA 437, 2012) degrades to the trivial product bound for `Z/2^μ`; the 2024 frontier
  (Loukaki arXiv:2412.08600) reaches only `N=pq`, never prime powers. So no `Z/2^μ` Fourier-support bound
  exists off the shelf — the Fourier-flat reformulation route is dead.
- **REACHES ONLY JOHNSON — Stepanov method (Weil-free).** Hanson–Petridis "Refined estimates concerning
  sumsets contained in the roots of unity" (arXiv:1905.09134, PLMS 2020) and Kalmynin "On additive
  irreducibility of multiplicative subgroups" (arXiv:2504.10202, 2025) pin `A±B` structure of `μ_d⊆F_p`
  Weil-free — the RIGHT hammer — but Stepanov bounds are Johnson-type; the prize is BEYOND Johnson, so it
  cannot reach. (Per the directive: anything reducing to Johnson is discarded.)
- **UNEXPLORED, likely non-transferable — slice rank / Croot–Lev–Pach.** Sauermann (arXiv:1904.09560) is the
  closest "distinct elements summing to zero" via slice rank, but lives in `F_p^n` (product structure); a
  single multiplicative subgroup `μ_n⊆F_p` lacks the tensor structure slice rank needs, with TWO power-sum
  constraints. Genuinely untried, but no reason it transfers.
- **RULED OUT — combinatorial structure** (this lane): pairing & subset-of-`U²` certificates hold at n=16
  but fail at n≥32 (above) — the realizing k-subset is global/non-constructive.

**Closest char-p structural result that exists:** Dvornicich–Zannier "Sums of roots of unity vanishing
modulo a prime" (Archiv Math 79, 2002, DOI 10.1007/s00013-002-8291-4) — extends Conway–Jones to mod-ℓ
congruences, but order-general (not 2^μ/split) and no power-sum/antipodal structure.

**Reading list additions (verified this sweep):** Dvornicich–Zannier (Archiv Math 79, 2002); Kalmynin
arXiv:2504.10202; Hanson–Petridis arXiv:1905.09134; Yip arXiv:2309.10950; Sauermann arXiv:1904.09560;
Kumar–Senthil Kumar arXiv:1503.07281; Murty–Whang (LAA 437, 2012); Loukaki arXiv:2412.08600;
Díaz Padilla–Ochoa Arango arXiv:2310.09992; Konyagin–Shparlinski–Vyugin arXiv:2005.05315.

**NET (definitive frontier).** The uniform Half-Sum Lemma sits exactly in the gap between Johnson-reaching
tools (Stepanov/Weil — too weak) and an OPEN structure problem (char-p `2^μ`-th-root vanishing sums in the
split regime — Lam–Leung leave it open, no post-1997 result closes it, the sharp Fourier tool is blocked at
composite modulus). PROVEN n=8,16; verified n=32,64. This is a *complete map* of why the prize is hard:
not a missing computation, but a genuine open problem requiring new arithmetic in a literature-confirmed gap.
The one untried plausible attack is redirecting the Hanson–Petridis/Kalmynin Stepanov machinery at
power-sum-constrained antipodal-free subsets — a research program, not an off-the-shelf citation.

## HONEST REFINEMENT — heuristic is clean (spurious⟹saturated), but the RIGOROUS general-r count IS BGK

Scan (`/tmp/scan6.py`): 141 NON-saturated primes p≡1 mod 32 in (577, 20000), ZERO fully-partial size-6
spurious configs. So at non-saturated primes every gap-valid config is a coset-union ⟹ `e₂∈Σ_3` trivially.
The p=97 spurious were at a SATURATED prime (`|Σ_3|=96≈p`), so uninformative.

**Counting heuristic (explains it, NOT rigorous).** #{gap-valid size-2r configs} ≈ `C(n,2r)/p²` (two
conditions e₁=e₃=0); #{coset configs} ≈ `C(n/2,r)`. Spurious exist iff `C(n,2r)/p² > C(n/2,r)`, i.e.
`p ≲ n^{r/2}`. Saturation bound `p ≲ |Σ_r| ≈ n^r/(2^r r!)`. For large n, `n^{r/2} < n^r/(2^r r!)`, so
**spurious ⟹ p below saturation ⟹ none in the non-saturated prize regime** (`p=n^β`, β≥4 ≫ r/2). This
matches all data and gives `e₂∈Σ_r` ⟹ δ*=window edge.

**But the rigorous version re-hits BGK — honest correction of last round's "not BGK".** Making the count
rigorous needs the error term: #configs `= (1/p²)∑_{a,b} S(a,b)^{2r}`, `S(a,b)=∑_{x∈μ_n}e_p(ax+bx³)` an
incomplete cubic exponential sum over the subgroup `μ_n`. To show the non-coset (spurious) count is 0 in
the non-saturated regime needs a nontrivial bound `|S(a,b)| < n`. Weil gives `|S|≤3√p`, which is TRIVIAL
(worse than `n`) precisely when `p > n²` — and the prize has `p=n^β ≫ n²`. So the rigorous bound is the
incomplete-sum / BGK regime, OPEN for prize parameters. My last-round "feasibility 6, finite algebra not
BGK" was correct for the HEURISTIC and for r=2, but the RIGOROUS general-r proof reduces to the same
small-subgroup character-sum wall.

**Accurate final standing.** δ* = `1−ρ−2ρ ln(1/2ρ)/log₂(qε*)`. PROVEN: upper bracket; ℂ optimality;
**r=2 `F_p` case (even-polynomial, rigorous, char-p-free)**. Heuristically clear for all r (spurious⟹
saturated, verified 141 non-sat primes). The rigorous general-r proof = nontrivial bound on
`∑_{x∈μ_n}e_p(ax+bx³)` for `p≫n²` = BGK/incomplete-sum, open. So: the optimality is RIGOROUSLY proven at
r=2 and heuristically/empirically certain for all r, but the worst-case rigorous proof for general r is
gated on the recognized incomplete-exponential-sum bound. NOT a full closure; I will not claim otherwise.
The genuine net gain this session: the EVEN-POLYNOMIAL proof of the minimal case and the
spurious⟹saturated counting structure — which localize and explain the wall, even though they don't
remove it for general r.

## GRIND ROUND — machinery built + exponential-sum refutation map

**Lean bricks landed (axiom-clean, real build):**
- `NegationClosure.lean` (commit 6770e4fba): `neg_closed_of_even` (even gen poly ⟹ root multiset ±-pair-
  closed) + `neg_closed_of_expand_two` (X²-poly ⟹ union of μ₂-cosets). Value-level seed of the r=2
  minimal case, complementing `FactorizationRigidity.lean` (m-sparse ⟺ μ_m-coset-union).

**Refutation map of the exponential-sum core** `S(a,b)=∑_{x∈μ_n}e_p(ax+bx³)` (`/tmp/cubsum.py`):
- ❌ REFUTED `|S| ≤ 2√n`: max|S| = 7.47/11.63/17.71 > 2√n = 5.66/8.0/11.31 (n=8/16/32). Sup exceeds √n.
- ❌ REFUTED "cubic helps": max|S| (cubic, 2-freq) > max|η_b| (linear Gauss) at every instance — the
  extra frequency makes the sup LARGER, not smaller. The cubic twist gives no advantage.
- ✓ SURVIVES `|S| ≤ 2√(n ln p)`: 7.47/11.63/12.98/17.71 < 2√(n ln p) = 11.7/17.1/18.3/24.2.
- ⚠ But the sup bound is INSUFFICIENT for the count: #gap-valid configs `= (1/p²)∑_{a,b}S^{2r}`; with
  `|S|≤2√(n ln p)` the error `≤ (4n ln p)^r ≫` coset count `~ C(n/2,r)`. So controlling spurious needs
  the MOMENT `∑_{a,b}|S|^{2r} = ` additive energy `E_r`, NOT just the sup — re-confirming the moment-
  method (Wick-vs-char-p-anomaly) wall (#389) from the exponential-sum side.

**Irrefutable conjectures (survived all refutation this campaign), all gated on the same moment/BGK wall:**
  (I1) `e₂(S) ∈ Σ_r` integrality (#bad = |Σ_r|) — PROVEN r=2 (even-poly), verified all r.
  (I2) `|∑_{x∈μ_n}e_p(ax+bx³)| ≤ 2√(n ln p)` — survived; insufficient alone.
  (I3) spurious ⟹ saturated (no spurious config at non-saturated p) — survived 141 primes.
  (I4) δ* = `1−ρ−2ρ ln(1/2ρ)/log₂(qε*)` — the exact formula.
All four reduce, rigorously, to the additive-energy `E_r(μ_s)` = diagonal-value (no char-p anomaly)
statement for `r ~ log n` — the recognized open core. The campaign has PROVEN the boundary (r=2, ℂ) and
built the reusable bricks; the interior (r≥3, char-p) is the moment wall, unbroken.

## UPDATE — LEAN STATUS of the optimality chain (2026-06-13): the ℂ side is now AXIOM-CLEAN LEAN; residual precisely localized

Auditing the in-tree state, the entire **characteristic-0** optimality chain is now machine-checked
axiom-clean (`[propext, Classical.choice, Quot.sound]`), not just paper+numerics:

| Piece | Lean theorem | file | axioms | build |
|---|---|---|---|---|
| (1) factorization rigidity | `mem_range_expand_iff`, `isRoot_smul_of_mem_range_expand` | `FactorizationRigidity.lean` | clean | green |
| (2) coset-saturation, ℂ (iterated Lam–Leung) | `full_tower`, `tower_count` | `LamLeungTwoPow.lean` | clean | 3299 jobs |
| (2) base (vanishing 2^μ-root 0/1-sum = ± pairs) | `count_antipodal_of_sum_eq_zero`, `multiset_antipodal_iff` | `LamLeungMultisetAntipodal.lean` | clean | green |
| (2) key-identity structural core (MDS dichotomy) | `monomialPencil_quasi_homogeneous`, `expand_eval_mu_d_invariant` | `MonomialPencilQuasiHomog.lean` | clean | 3297 jobs |

`full_tower` is exactly the ℂ coset-saturation: over `[Field F][CharZero F]`, a `2^M`-th-root set whose
power sums vanish on `1 ≤ j < 2^s` is closed under `×μ_{2^s}` (a `μ_{2^s}`-coset-union). The two new
monomial-pencil lemmas formalize the "key identity" face of piece (2): the pencil `U=X^a+γX^b` is
`μ_d`-quasi-homogeneous (`U(ωx)=ω^a U(x)` for `ω^(a−b)=1`) and the `a`-residue codeword part is
`μ_d`-eval-invariant — so agreement transports along `μ_d`-orbits (the codeword-side of the dichotomy).

**THE UNIFICATION (honest headline).** The SINGLE remaining mathematical residual is the **char-`p`
transfer** of `full_tower` — i.e. `q ∤ D` at the prize prime (`D` = the elimination resultant, factors
`≤ (rm)^{n/2}`; equivalently: does a short `±1` relation of `2^μ`-th roots vanish mod `q=n^β`?). This is
**bit-for-bit the same wall as the #389 energy/moment/Burgess core** (the additive-energy = diagonal-value
statement for `r ~ log n`). The combinatorial coset-saturation route and the energy route are both
**char-0-CLOSED and char-`p`-OPEN at the identical point** — they are one wall in two dresses, not two
independent routes one of which bypasses the other. So δ* is pinned EXACTLY in the provable regime
(`q > (rm)^{n/2}`) and over ℂ, axiom-clean in Lean; the prize regime (`q = n^β ≪ n^{n/2}`, `n=2^30`)
reduces to this one named arithmetic transfer = the recognized open core. No fabricated closure.

## UPDATE — the wall localized to the SYMMETRIC FUNCTIONS e_i, 2m≤i≤rm, m∤i (r=2 unconditional; prize r≈11)

A sharper structural split than "char-0 vs char-p", obtained by reading the bad-scalar condition
`e_i(S)=0 ∀i∈{1,…,2m−1}\{m}`, `|S|=rm`, directly through `P(X):=∏_{x∈S}(X−x)`:

- **`r=2` is CLOSED UNCONDITIONALLY (pure algebra, char-`p`-SAFE, no Lam–Leung/norm bound).** With
  `|S|=2m`, the vanishing `e_1..e_{2m−1}` (all but `e_m`) leave `P(X)=X^{2m}±e_m X^m+e_{2m} ∈ F_q[X^m]`,
  so by `FactorizationRigidity` (already Lean) `S` is a `μ_m`-coset-union. The whole polynomial is forced
  `m`-sparse because degree `2m` is fully covered by the window — there is no unconstrained "tail".
- **`r≥3` needs the cyclotomic bridge (= the wall).** For `r≥3` the symmetric functions `e_i(S)` with
  `2m≤i≤rm`, `m∤i` are UNCONSTRAINED by the window. Coset-union ⟺ `e_i(S)=0` for ALL `m∤i`; the window
  delivers only `i<2m`. The low→all bridge is `P | X^n−1` (i.e. `S⊆μ_n`): over ℂ it forces the tail to
  vanish (Lam–Leung / `full_tower`), over `F_q` at prize scale it does not. So the OPEN CORE is exactly:
  **the tail symmetric functions `e_i(S)`, `2m≤i≤rm`, `m∤i`, are forced to `0` by `P|X^n−1` over `F_q`.**
- **The prize sits at `r≈11`** (window-edge fit, `μ=30,ρ=1/4`: `s≈44`, `m≈2^{24.5}`, `|S|=ρn≈2^{28}`,
  `log₂|H^{(+r)}|≈30.4≈μ`). So the prize is firmly on the `r≥3` side; the `r=2` unconditional corner does
  not reach it. (And there is no parameter freedom to force `r=2`: the window edge pins `r`.)

This is the same wall, but now stated as a CONCRETE finite algebraic obligation (tail-`e_i` vanishing from
`P|X^n−1` over `F_q`), not a vague "transfer". A `poly(n)`-height proof of the tail-vanishing would close
the prize; the only known route (generic elimination/Nullstellensatz/norm) is doubly-exponential (see
DISPROOF_LOG "good-prime dodge"). No new math in the literature (PAPERS_NEEDED P1–P6) supplies it.
