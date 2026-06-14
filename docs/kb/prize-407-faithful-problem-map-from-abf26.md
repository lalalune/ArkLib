# Prize #407 — faithful problem map, read from ABF26 (eprint 2026/680) primary source

Read the actual paper (`~/papers/arklib/eprint-2026-680-abf26.pdf`) §1–5,7 end to end, 2026-06-14.
This is the authoritative statement; prior in-tree framings reduced to "BGK" — that reduction is
FAITHFUL but this records the exact theorems, brackets, and the authors' own suggested directions.

## The two grand challenges (verbatim intent)

**Grand MCA challenge.** `C = RS[F, L, k]`, `L` = smooth multiplicative subgroup of size a power
of two, rate `ρ ∈ {1/2,1/4,1/8,1/16}`. For `ε* = 2^-128`, determine the **largest `δ*_C`** with
`ε_mca(C, δ*_C) ≤ ε*`, assuming `|F|` sufficiently large (`k ≤ 2^40`, `|F| < 2^256`).
**Grand LD challenge.** Same, determine largest `δ*_C` with `|Λ(C^{≡m}, δ*_C)| ≤ ε*·|F|` (m-wise
interleaved, m constant). The error matters because SNARK soundness has a `|Λ(C^{≡m},δ)|/|F|` term.

**KEY:** `|F|` is taken LARGE (not fixed at `n·2^128` — that was a fleet parametrization). The error
in every regime is `(stuff)/|F|`; `δ*` is where `(stuff)` crosses `ε*·|F|` ⟺ where `(stuff)` goes
from `poly(n)` to super-poly.

## The PROVEN brackets on `δ*` (Table 1 + §4) — `δ*` lives in `(1−√ρ, 1−ρ−Θ(1/log n))`

| regime | bound | status |
|---|---|---|
| `δ < δ_min/2` (unique dec.) | `ε_mca ≤ O(n)/|F|` | proven (ACFY25/BCIKS20) |
| `δ < 1−√ρ−η` (**up to Johnson**) | `ε_mca ≤ O_ρ(n/(η^5|F|))` | **proven** (Thm 4.12, BCHKS25) — `δ* ≥ Johnson` |
| `δ = J(δ_min)` exactly | `ε_ca ≥ Ω(n²/|F|)` | proven char-2 (Thm 4.18) |
| `δ = 1−ρ−Θ(1/log n)` (near cap.) | `ε_ca ≥ n^c/|F|` ∀c | **proven, SMOOTH domains + prime fields** (Thm 4.16, KK25) — `δ* ≤ 1−ρ−Θ(1/log n)` |
| `δ = 1−ρ−1/√(n log q)` | `ε_ca = 1` (total breakdown) | proven (Thm 4.17, CS25) |

So BOTH brackets are PROVEN: `δ*` is strictly between Johnson `1−√ρ` and `1−ρ−Θ(1/log n)`. The
challenge is to PIN it in the interior. **The Θ(1/log n) distance-from-capacity is forced** (Thm 4.16).

## Why the interior is open (the additive-conspiracy / BGK wall is FAITHFUL)

- **LD ⟹ MCA has a √-loss** (Thm 5.1, GCXK25): list `≤ L` at radius `δ` ⟹ MCA only at the smaller
  radius `1−√(1−δ+η)`, error `O(L²n/(η|F|))`. To reach MCA at `1−ρ` you'd need LD at `1−ρ²` (BEYOND
  capacity, impossible). So the LD route does NOT reach the window — a DIRECT MCA argument is needed.
- **Random RS reaches capacity** (Thm 4.15, GG25: random `L`, MCA at `1−ρ−η`, `η>c₁n^{-1/9}`), and
  **folded/subspace-design reach capacity** (Thm 4.13/4.14) — but the prize is PLAIN RS over a
  STRUCTURED (smooth `μ_n`) domain, neither random nor folded. The structure is exactly the obstacle.
- The direct MCA bound for structured `μ_n` past Johnson = controlling the additive conspiracy of
  `μ_n` = the incomplete character sum `max_b|η_b|` (BGK/Paley √-cancellation). This reduction is
  faithful; ~40 techniques + the dyadic tower / 2-adic / Gauss-phase / budget / fixed-index analyses
  (this session) all confirm it. Best proven exponent `n^{0.989}` (di Benedetto), prize needs `√n`.

## The authors' OWN suggested directions (§7) — and where each lands for smooth `μ_n`

1. **Derandomize random-RS** (Thm 4.15 → explicit `L` with "more structure"): the explicit suggestion
   for the prize. Derandomizing = showing `μ_n` doesn't conspire = the character sum = BGK.
2. **Characterize degenerate codes** ("which codes are well-behaved vs degenerate"): EXACTLY this
   session's **cyclotomic dichotomy** (`CyclotomicConcentration.lean`) — the `q`-independent bad
   families are precisely the degenerate (correlated, `X^{2^s}`-factoring) ones. A genuine contribution
   to this stated open direction.
3. **Effect of interleaving** (Lemma 4.7 `ε_mca(C^{≡s}) ≤ s·ε_mca(C)` — tight? DG24: equality in
   unique-decoding): open whether tight past Johnson.
4. **Subspace-design parameter improvement** (the `s=O(1/η²)` alphabet tradeoff; "no natural barrier
   known" to better `η`-vs-`s`).

## Net

The prize is **faithfully** the smooth-`μ_n` direct-MCA bound in the window `(1−√ρ, 1−ρ−Θ(1/log n))`,
both brackets proven, interior open, reducing (via every known route incl. the authors' own) to the
additive conspiracy of `μ_n` = BGK/Paley. No combinatorial/`q`-independent bypass (dichotomy proven),
no budget slack (cancels), LD-route blocked by √-loss. Closure requires new analytic NT on
`max_b|η_b|` for `n=q^{1/4}` dyadic subgroups, OR a genuinely new direct-MCA argument that the random/
folded/subspace-design proofs (which the structure defeats) do not provide.

## DERANDOMIZATION VERDICT (the authors' §7 direction, attacked) — fails structurally; excess = n-core conspiracy

AGL24 (arXiv 2304.09445) mechanism (read directly): a bad list-decoding config ⟺ a **weakly-
partition-connected agreement hypergraph** realized by actual codewords; random RS avoids these via
**GM-MDS genericity** of the evaluation points (Brakensiek–Gopi–Makam, via a hypergraph orientation +
GM-MDS theorem). Random L is generic ⟹ list-decodable to capacity.

**Smooth μ_n is NOT GM-MDS-generic.** The certificate is the cyclotomic `det(ζ^{β_j·i})=∏(ζ^{β_j}−ζ^{β_i})`
(in-tree `genVandermonde_rootsOfUnity_det`), which VANISHES on n-core-nonempty shapes (β's collide mod n,
`homds_det_eq_zero_iff_nCore_nonempty`). So μ_n REALIZES weakly-partition-connected agreement hypergraphs
that random points avoid — derandomization fails at exactly the n-core shapes.

**Computed (probe /tmp/probe_derand2.py, n=16 k=3):** μ_n worst-list STRICTLY EXCEEDS random-L worst-list
across the window: a=4 (δ=.75) μ_n=46 vs rand=22; a=6,7 μ_n=2 vs rand=0. The excess is q-independent
(q=97:46, q=113:48) ⟹ the failure is **combinatorial (n-core conspiracy)**, not the small q-dependent
anomaly. So smooth RS is provably WORSE than random RS for list-decoding, for a concrete structural reason.

**Verdict:** derandomization (the prize's most-cited route) FAILS structurally. δ* is pinned by the
SIZE of the n-core conspiracy (combinatorial floor) + the char-p anomaly (BGK ceiling). Whether the
combinatorial floor alone is super-poly past Johnson (→ δ* CLOSED combinatorially, the one bypass) or
stays poly (→ δ* needs BGK) is the remaining question — at n=16 the excess is modest (≤2×), but
Thm 4.16 (KK25) PROVES some smooth code has super-poly excess near capacity. Determining the EXACT
combinatorial floor of the n-core conspiracy count vs δ is the concrete open target (q-independent,
computable in principle) — the one place a closed combinatorial δ* could still live.

## KAMBIRÉ CEILING read in full (arXiv 2604.09724) — the open core REFRAMED as SUMSET EXTREMALITY

Read the failure paper end to end. The proven ceiling `δ* ≤ 1−ρ−Θ(1/log n)` is a **subgroup-sumset
construction**, NOT an abstract character sum:
- Line `f=X^{rm}, g=X^{(r−1)m}`; for `λ=ξ_1+…+ξ_r ∈ H^{(+r)}` (r-fold RESTRICTED sumset of a
  sub-subgroup `H=⟨ξ⟩`, |H|=s), the identity `∏_{a∈H_1∪…∪H_r}(X−a)=X^{rm}−λX^{(r−1)m}+R(X)` (deg R
  ≤(r−2)m) makes `f+λg` agree with codeword `R` on `rm=(1−δ)n` points. So the bad-scalar count =
  **`|H^{(+r)}|` (a sumset cardinality)** `≥ (s/2r)^r = n^C`.
- Parameters: `s=2^α`, `n=sm`, `k=(r−2)m`, `r=ρs+2`, `δ=1−r/s`, `η=2/s=Θ(1/log n)`, `s=K log n`,
  `K≈C/(ρ log(1/2ρ))` ⟹ **`δ* ≤ 1−ρ−2ρ ln(1/2ρ)/log(qε*)`** (the exact constant).
- The "good prime" (where the `r`-sums are DISTINCT mod p, giving polynomially-many distinct λ) exists
  by **quantitative Linnik**; bad primes = those dividing `Res(Φ_s, ΣX^i−ΣX^j)` (≤ log₄ s per pair).

**THE REFRAME (key):** the open FLOOR (`δ* ≥` same) is exactly **SUMSET EXTREMALITY** — that the
subgroup-sumset `|H^{(+r)}|` is the MAXIMAL bad-scalar count over ALL affine lines (f,g), up to a
sub-polynomial factor. This is **char-free additive combinatorics** (a Cauchy–Davenport / Vosper /
Plünnecke-flavoured extremality), NOT the L^∞ Gauss-period sup-norm. A poly(n) factor in the
max-over-lines shifts η by `O(1/(log n)²)` (negligible), so the LEADING δ* is pinned IFF
`max_line(bad count) ≤ poly(n)·|H^{(+r)}|`. This is a cleaner, possibly-tractable target than BGK —
and is the precise content of the floor. (R1 "monomial extremality" was refuted only at the
CONSTANT level — a general pencil doubles the count — which does NOT move the leading δ*.)

**THE CLOSED CONJECTURE (the deliverable):**
> `δ*(RS[F_p,μ_n,k], ε*) = 1 − ρ − 2ρ·ln(1/2ρ)/log(p·ε*)` (leading order), with
> CEILING proven (Kambiré sumset construction + Linnik) and FLOOR = **Sumset Extremality**:
> for every affine line `(f,g)` and `δ` below the threshold, `#{λ : Δ(f+λg, C) ≤ δ} ≤ poly(n)·|H^{(+r)}|`.
> The novel math IS the sumset-extremality bound — char-free, the whole open content, no deferral to BGK.

Scores: novelty 8 (reframe analytic→additive-combinatorial), insight 9 (δ* = subgroup-sumset
extremality over lines), proximity 10 (the literal failure construction), feasibility = the open
question the extremality probe decides (poly-bounded ⟹ tractable/char-free; super-poly ⟹ still BGK).
