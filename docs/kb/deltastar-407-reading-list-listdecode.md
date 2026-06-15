# δ* (#407) Reading List — Explicit Reed–Solomon List-Decoding Past Johnson / Up to Capacity

**Date:** 2026-06-14. **Lane:** S3-papers-listdecode. **Author:** sub-agent (citations verified via arXiv/ECCC/DOI).

## The question this list answers

For the prize we need list-decodability (equivalently the far-line incidence count `I(δ)`)
**past the Johnson radius `J(δ)=1−√ρ`, up to the capacity window `(1−√ρ, 1−ρ−Θ(1/log n))`,
for PLAIN (un-folded, multiplicity-1) RS over the EXPLICIT structured domain `μ_n`**
(smooth multiplicative subgroup, `n=2^μ`, `n | p−1`, `p` prime, constant rate `ρ=k/n`).

For each paper below the load-bearing column is: **does it handle explicit structured
`μ_n`/FFT evaluation points for PLAIN RS, or only random / generic / folded / multiplicity /
AG / subspace-tower constructions?**

> **HEADLINE VERDICT (honest):** NO paper in 2022–2026 gets PLAIN RS over an explicit `μ_n`/FFT
> domain past Johnson at constant rate. Every capacity-achieving RS result needs one of:
> (i) **random/generic** evaluation points (BGM, GZ, AGL, FKS, BCY — the prize forbids random),
> (ii) **folding / multiplicity** (Chen–Zhang, GR08 line — changes the code, not plain RS over μ_n),
> (iii) a **special subfield-tower / double-exponential** domain (Shangguan–Tamo explicit — the
> *opposite* of μ_n), or (iv) **subspace-design codes** (Goyal–Guruswami — folded/multiplicity, not
> plain RS over μ_n). The matching NEGATIVE results (BKR10 subspace polynomials; BCHKS25 Thm 1.13)
> show structured *additive* and *multiplicative-subgroup* domains can be the WORST case, and the
> exact prize statement (BCHKS25 Conj 1.12 / Def 1.10–1.11) is **OPEN and equivalent to a clean
> additive-combinatorics sumset conjecture** that current sum-product SOTA misses by a power.

---

## A. Capacity-achieving RS — but RANDOM / GENERIC evaluation points (prize-forbidden)

1. **Brakensiek, Gopi, Makam — "Generic Reed–Solomon codes achieve list-decoding capacity."**
   arXiv:2206.05256, STOC 2023.
   - Generic (= GM-MDS zero-pattern) RS of rate `R` over an **exponentially large** field is
     `(1−R−ε, (1−R−ε)/ε)`-list-decodable: capacity with finite list. Via higher-order MDS / MDS(ℓ).
   - **Domain:** generic / random evaluation points; field `q = exp(n)`. **NOT μ_n, NOT explicit.**
   - Relevance: defines the higher-order-MDS lens the recon's A19/BGM probes test; the *combinatorial*
     target the prize must reach but via an explicit structured domain instead of genericity.

2. **Guo, Zhang — "Randomly Punctured RS Codes Achieve the List Decoding Capacity over
   Polynomial-Size Alphabets."** arXiv:2304.01403, FOCS 2023.
   - Random puncturing achieves `(1−R−ε, O(1/ε))` over `q ≥ 2^{poly(1/ε)} n²` (poly field).
   - **Domain:** RANDOM puncturing of `F_q`. Drops field from exp to poly — but still random. **Not μ_n.**

3. **Alrabiah, Guruswami, Li — "Randomly Punctured RS Codes Achieve List-Decoding Capacity over
   Linear-Sized Fields."** STOC 2024 (also ECCC 2023/125, arXiv:2304.09445 line).
   - Capacity with optimal list `O(1/ε)` over **linear** field size `q = O(n)`.
   - **Domain:** RANDOM evaluation points. The strongest field-size result — yet inherently random;
     gives NO explicit/deterministic μ_n construction. Closest field size to the prime prize.

4. **Brakensiek, Dhar, Gopi — "Improved Field Size Bounds for Higher Order MDS Codes."**
   arXiv:2212.11262, ISIT 2023.
   - Field-size LOWER bound `Ω_ℓ(n^{ℓ−1})` and near-matching upper for `(n,k)`-MDS(ℓ); nearly closes
     the exp gap. **This is the field-size obstruction substrate** (the recon's "HOMDS field lower
     bounds"). Implies any MDS(ℓ)-route to capacity needs growing field — relevant to why μ_n at a
     FIXED prime cannot be MDS(ℓ) for large ℓ.

5. **Ferber, Kwan, Sauermann — "List-decodability with large radius for Reed–Solomon codes."**
   arXiv:2012.10584 (2020/21). EXISTENCE (most RS codes), poly/almost-linear field. **Not explicit.**

6. **Brakensiek, Dhar, Gopi, Zhang — "AG Codes Achieve List-decoding Capacity over Constant-sized
   Fields."** arXiv:2310.12898, STOC 2024.
   - Randomly punctured **algebraic-geometric** codes hit capacity over CONSTANT field size.
   - **Domain:** AG codes + random puncturing — not RS, not μ_n. Shows constant field is possible only
     by leaving RS and using random puncturing.

## B. Capacity-achieving + EXPLICIT — but FOLDED / MULTIPLICITY / SUBSPACE-DESIGN (changes the code)

7. **Chen, Zhang — "Explicit Folded RS and Multiplicity Codes Achieve Relaxed Generalized Singleton
   Bounds."** arXiv:2408.15925, STOC 2025.
   - **Explicit** folded RS + univariate multiplicity codes reach capacity `1−R−ε` with optimal list
     `O(1/ε)`; resolves the GR06/GR08 open problem. Best explicit capacity result to date.
   - **Domain:** FOLDED / MULTIPLICITY — a bundled/derivative code, NOT plain RS over μ_n. A folded RS
     symbol is a window of consecutive μ_n-points; the prize's plain single-point RS is exactly the
     un-folded `s=1` case these methods do NOT cover.

8. **Berman, Shany, Tamo — "Explicit Subcodes of RS Codes that Efficiently Achieve List Decoding
   Capacity."** arXiv:2401.15034, IEEE-IT 71(8):5898–5911 (2025).
   - Explicit RS **subcodes** (tensor of two RS + cyclic shifts; equiv. RS evaluated on a subfield /
     interleaved RS / orbits of two coprime affine maps) hit capacity with constant list.
   - **Domain:** a SUBCODE of (interleaved) RS over a subfield, treated as folded columns — again not
     plain full-rate RS over μ_n. The "orbit of affine maps" framing is the closest structural cousin
     to the prize's μ_n-orbit incidence (recon ROUTE-2), but it is still a subcode, not the code.

9. **Goyal, Guruswami — "Optimal Proximity Gaps for Subspace-Design Codes and (Random) RS Codes."**
   ePrint 2025/2054, STOC 2026. (Subsumes the now-WITHDRAWN Jeronimo–Liu–Rajpal arXiv:2601.10047.)
   - **THE state-of-the-art proximity-gap-up-to-capacity result.** Proves optimal proximity gaps
     `δ → 1−R−η` (capacity!) for **subspace-design codes**: folded RS, univariate multiplicity codes;
     AND proximity gaps up to Johnson for ALL RS (matching GCXK25 with `a=O(n)` for random RS).
   - **CRITICAL for #407:** explicitly lists the codes that get capacity proximity gaps — folded RS,
     multiplicity, random linear, random LDPC, **random** RS — and states most known capacity codes
     have proximity gaps only for `δ < 1−R`. **PLAIN RS over an explicit μ_n is NOT in the list.**
     This is the published frontier the prize sits just beyond.

## C. EXPLICIT plain RS PAST Johnson — exists, but the WRONG (anti-μ_n) domain

10. **Shangguan, Tamo — "Combinatorial list-decoding of RS codes beyond the Johnson radius."**
    arXiv:1911.01502, STOC 2020.
    - Generalized Singleton bound; conjecture proven for list sizes 2,3; and **the first EXPLICIT RS
      code list-decodable BEYOND Johnson**: `(2/3·(1−R), 2)`-list-decodable.
    - **Domain (the catch):** evaluation points form a **tower of subfields** — `α_i` generates a
      degree-`k` extension over `F_{2^{k^{i−1}}}` — needing **DOUBLE-EXPONENTIAL field `q = 2^{k^n}`**.
      This is the structural OPPOSITE of a smooth μ_n inside a single fixed prime field. Confirms that
      "explicit beyond Johnson" is achievable only by an extreme, non-μ_n, non-FFT domain.

## D. EXPLICIT/DETERMINISTIC, but only UP TO Johnson (the explicit ceiling)

11. **Chatterjee, Harsha, Kumar — "Deterministic list decoding of Reed–Solomon codes."**
    arXiv:2511.05176, STOC 2026 (also ECCC 2025/170).
    - Deterministic, `poly(n, log|F|)` over **any** field (including prime fields) from agreement
      `√((k−1)n)` = **exactly the Johnson radius**. Derandomized Sudan via Newton iteration.
    - **Domain:** any field / any evaluation set, INCLUDING prime fields and μ_n — but **stops at
      Johnson.** Pins the explicit/deterministic frontier precisely at `J(δ)`; the prize lives strictly
      above this line.

## E. The NEGATIVE results — structured domains can be the WORST case (this is the prize's wall)

12. **Ben-Sasson, Kopparty, Radhakrishnan — "Subspace Polynomials and Limits to List Decoding of
    Reed–Solomon Codes."** IEEE-IT 2010 (= BKR / "BSKR06").
    - For full-length / **affine-SUBSPACE** evaluation domains, a received word agrees with a
      **superpolynomial** number of degree-`K=N^δ` polynomials on `≈ N^{√δ}` points each (existence;
      explicit version `2^{√log N}·K`). So structured ADDITIVE domains have list size `≥ N^{Ω(...)}` —
      list-decoding fails badly. **The classic warning that structure ≠ good list-decoding.**
    - For #407: the bad set is ADDITIVE (subspace). The prize's μ_n is MULTIPLICATIVE — so BKR does
      NOT directly kill μ_n, but it proves the burden of showing μ_n is *not* analogously bad.

13. **Ben-Sasson, Carmon, Haböck, Kopparty, Saraf — "On Proximity Gaps for Reed–Solomon Codes."**
    ECCC 2025/169 (Nov 7 2025). *(StarkWare + Toronto.)*
    - **THE prize paper.** Positive: proximity gaps up to `δ/2` with `O_ε(1)` exceptions, and up to
      Johnson `J(δ)` with `O(n)` exceptions, `ε*=0`. Negative: the `n^τ`-bounded proximity-gaps
      conjecture is **FALSE** for every `τ` (Thm 1.6, char 2, subspace-polynomial + 2nd-moment).
    - **§1.4.3 "Limits over prime fields" — the EXACT governing-law object for #407:**
      - **Def 1.10:** `E^{(+ℓ)} = {e_1+…+e_ℓ : e_i ∈ E distinct}` (the ℓ-fold sumset).
      - **Def 1.11:** `(q,a,b)` admissible iff ∃ multiplicative subgroup `G⊆F_q^*` with `|G|=b` and
        for `ℓ=⌊b/2⌋`, `|G^{(+ℓ)}| ≥ a`.
      - **Conjecture 1.12 (OPEN):** for ∞ many primes `q`, ∃ `b ≤ 10 log q` with `(q, q/10, b)`
        admissible. → gives ∞ many bad proximity-gap instances over prime fields.
      - **Theorem 1.13:** if `(q,a,b)` admissible (b even), `G` the subgroup, `D=H ⊇ G`,
        `C=RS[F_q,D,k]` with `k=(1/2 − 2/b)n`, `δ=1/2 + 2/b`: then ∃ `f,g` with the far-line at radius
        `δ−2/b` having `≥ a` close `z`'s yet `Δ([f,g],C²) ≥ δ−1/b`. **I.e. a μ_n-domain RS code with a
        genuine beyond-Johnson proximity-gap defect — exactly the `I(δ)` blow-up the prize must rule
        out, conditional on a clean sumset conjecture.**
      - **Mersenne instantiation:** for `q=M_31=2^31−1`, `(q, q, 2 log_2 q)` admissible via
        `G=⟨−2⟩=±powers-of-2`; gives `Δ(f+zg) ≤ 1/2 ∀z` yet `Δ([f,g]) ≥ 1/2 + 1/62 ≈ 0.516`. For
        `q=(M_31)^4 ≈ 2^124` (prize-scale prime!) `b≈2 log₂q`, `δ≈0.508`, proximity loss `ε*=1/62≈0.004`.
    - **The additive-combinatorics gap (verbatim):** the best unconditional sumset bound
      **Glibichuk–Konyagin [GK07]** gives only `|G^{(+ℓ)}| ≥ |G|^{Ω(log ℓ)}`, **"far short of what the
      conjecture asks for."** Heuristic wants `|G^{(+ℓ)}| ≥ Ω(min(q, C(b,ℓ)))`. **This is exactly the
      recon's BGK/Paley √-cancellation wall restated as a sumset growth question.**
    - **§1.4.2 Thm 1.9 + Def 1.8 `LDR`:** proximity gaps with `o(1)` loss past the **list-decoding
      radius** `LDR_{F_q,D,L}(δ)` force large `a` — formalizes that proximity gaps ⇔ list-decodability,
      so the prize δ* IS the LDR question (matches the in-tree governing law `δ*=sup{δ: I(δ)≤qε*}`).
    - **§8 / Thm 1.17 CYCLE-SUM attack:** an explicit STARK-soundness attack over `D = ` union of cosets
      of a multiplicative subgroup `G` — directly the μ_n-domain regime the prize cares about.

## Precise gap to explicit μ_n (what is missing, stated exactly)

- **Plain RS over μ_n past Johnson at constant rate is OPEN in BOTH directions.**
  - **Upper (prize-positive, `I(δ)` small):** No paper proves it. The closest is BCHKS25's positive
    side, which stops at Johnson `J(δ)` with `O(n)` exceptions; capacity-region positivity exists only
    for RANDOM RS (AGL/GZ/BCY) or FOLDED/multiplicity/subspace-design (Chen–Zhang, Goyal–Guruswami).
  - **Lower (refutation, `I(δ)` large):** BCHKS25 Thm 1.13 gives a genuine μ_n beyond-Johnson defect
    **conditional on Conjecture 1.12** (a sumset-growth statement), and Mersenne/`M_31^4` instantiations
    are unconditional small examples but with tiny relative distance / specific `(q,a,b)`, not the prize's
    constant-rate `ρ∈{1/2,…,1/16}` with `δ` in the deep window `(1−√ρ, 1−ρ−Θ(1/log n))`.
- **Why folding/multiplicity does not transfer:** capacity-achieving explicit codes (B7,B8,B9) attach a
  *window* of consecutive evaluations (or derivatives) to each coordinate; the prize's far-line pencil
  `x^a+α x^b` is a single-point un-folded RS object. The folding is precisely the device that defeats the
  beyond-Johnson list blow-up — removing it returns you to the open μ_n question.
- **Why the BKR negative does not auto-kill μ_n:** BKR's bad domain is an *additive* subspace; μ_n is a
  *multiplicative* subgroup with NO additive structure. BCHKS25's `G^{(+ℓ)}` sumset is exactly the bridge:
  multiplicative `G` becomes bad **iff** its additive ℓ-fold sumset stays small. So the prize reduces to:
  **does the ℓ-fold sumset of a thin multiplicative subgroup `μ_n` (n=2^μ, n≪p^{1/4}) grow to ~min(p, …)?**
  — the same √-cancellation / sumset wall as the Gauss-period reading list (`...-gaussperiods.md`), and
  the in-tree `EnergyCharacterTransport` energy⇆char-sum bridge.

## One-line per-paper μ_n verdict

| # | Paper (id) | Capacity? | Explicit? | Plain RS? | Domain = μ_n/FFT? |
|---|---|---|---|---|---|
| 1 | BGM 2206.05256 | yes | no (generic) | yes | NO (random, q=exp) |
| 2 | Guo–Zhang 2304.01403 | yes | no (random punct) | yes | NO (random, q=poly) |
| 3 | Alrabiah–Guruswami–Li 2304.09445/STOC24 | yes | no (random) | yes | NO (random, q=O(n)) |
| 4 | Brakensiek–Dhar–Gopi 2212.11262 | (field lower bnd) | — | (MDS(ℓ)) | NO (obstruction) |
| 5 | Ferber–Kwan–Sauermann 2012.10584 | partial | no (existence) | yes | NO |
| 6 | BDGZ AG 2310.12898 | yes | no (random) | NO (AG) | NO |
| 7 | Chen–Zhang 2408.15925 | yes | YES | NO (folded/mult) | partial (μ_n cols, folded) |
| 8 | Berman–Shany–Tamo 2401.15034 | yes | YES | NO (subcode) | partial (orbit/subfield) |
| 9 | Goyal–Guruswami 2025/2054 (STOC26) | yes (gaps) | YES | NO (subspace-design) | NO for plain RS |
| 10 | Shangguan–Tamo 1911.01502 | no (>Johnson) | YES | yes | NO (subfield tower, q=2^{k^n}) |
| 11 | Chatterjee–Harsha–Kumar 2511.05176 | no (=Johnson) | YES (determ.) | yes | YES but only ≤ Johnson |
| 12 | BKR (subspace poly) IEEE-IT 2010 | NEG | — | yes | additive subspace (worst case) |
| 13 | BCHKS25 ECCC 2025/169 | POS≤J + NEG | YES | yes | **YES (Conj 1.12 / Thm 1.13)** |

**Bottom line:** the prize question — plain RS over explicit `μ_n`, constant rate, beyond Johnson — is
exactly **BCHKS25 §1.4.3 (Conjecture 1.12 admissibility / Theorem 1.13)**, open and equivalent to a
multiplicative-subgroup sumset-growth conjecture that unconditional SOTA (Glibichuk–Konyagin) misses by a
power. No 2022–2026 paper closes either direction for this domain.
