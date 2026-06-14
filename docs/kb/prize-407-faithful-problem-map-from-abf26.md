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
