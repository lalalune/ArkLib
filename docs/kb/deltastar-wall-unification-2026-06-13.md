# The wall is one wall: all faces collapse to `E(μ_n)` via the pairwise/Johnson barrier (2026-06-13)

A synthesis derived and numerically verified this session. It proves, by an elementary argument
plus the ABF26 bridge, that the LD-window, the MCA-window, and the additive-energy exponent are
**the same obstruction**, and pins exactly where any prize attack must inject *new* (≥3-wise)
structure. This is the honest map of why every face routes through `E(μ_n)=n^{2+o(1)}`.

## 1. The elementary Fisher bound IS the Johnson radius (full derivation)

List of `L` codewords `c_1,…,c_L` (deg `<k`), each agreeing with received `w` on `S_i ⊆ μ_n`,
`|S_i| = a = (1−δ)n`.
- **Pairwise:** `c_i − c_j` is a nonzero deg-`<k` poly ⇒ `|S_i ∩ S_j| ≤ k−1`.
- **Double count** with `deg(x) = #{i : x∈S_i}`: `Σ_x deg(x) = La`, and
  `Σ_x C(deg(x),2) = Σ_{i<j}|S_i∩S_j| ≤ C(L,2)(k−1)`.
- **Jensen** (`Σ_x C(deg(x),2) ≥ n·C(La/n,2)`) ⇒
  `(La/2)(La/n − 1) ≤ L(L−1)(k−1)/2`, which solves to
  > **`L ≤ (a−k+1)·n / (a² − (k−1)·n)`.**
- **Finite iff** `a² > (k−1)n` ⟺ `(1−δ)²n > k` ⟺ `δ < 1 − √ρ` = **Johnson**. The bound
  **diverges at Johnson** and is **vacuous beyond it**.

So the *only* elementary structural fact (pairwise intersections `< k`) gives **exactly** Johnson —
not one step further. The smooth domain `μ_n` does **not** change this step (it never used the
domain structure beyond "`<k` roots"). **Verified numerically** (`probe_fisher_johnson_boundary.py`):
the actual worst-case structured-word list stays `≤` the Fisher bound below Johnson, and every list
explosion (e.g. `715` at `n=16,k=6`) occurs precisely where `a ≤ √((k−1)n)` and the bound is `inf`.

## 2. The ABF26 `√`-loss is the SAME pairwise barrier

ABF26 Thm 5.1: `Λ(C,δ_LD) ≤ L ⇒ ε_mca(C, 1−√(1−δ_LD)) ≤ L²·δ_LD·n/|F|`. Invert to ask for MCA at a
target window radius `δ`: need `δ_LD = 2δ−δ² = 1−(1−δ)²`. At `δ = capacity = 1−ρ`,
`δ_LD = 1−ρ² > 1−ρ` — **list decoding beyond capacity, impossible**. So the bridge **cannot reach
the window's upper part for any code**; even random RS (list-decodable to capacity) only yields MCA
up to **Johnson** via Thm 5.1. The `√` is the Johnson transform — the *same* pairwise/second-moment
step as §1. **MCA-window = LD-window = the place the pairwise bound dies = Johnson.**

## 3. Therefore: breaking Johnson ⇔ controlling ≥3-wise coincidences = the additive energy

Beyond Johnson the pairwise count is vacuous; a finite list bound requires bounding **triple and
higher coincidences** `Σ_x C(deg(x),3+)`, i.e. how often three+ list codewords meet. For RS on a
multiplicative subgroup these higher coincidences are governed by the **additive energy
`E(μ_n) = Σ_t r(t)²`** and its higher moments (the `c_i−c_j` differences are deg-`<k` polynomials
whose common roots on `μ_n` are exactly additive-coincidence counts). The sharp value
`E(μ_n)=n^{2+o(1)}` is precisely what converts the vacuous Johnson bound into a finite window list
bound at the prize budget. **Every face — list (i), character sums (ii), census/bad-family (iii),
line–ball incidence (iv), curve-irreducibility (v), and the MCA bridge — injects its new structure
at this same triple-coincidence/energy step.** That is why they are inter-reducible and why none
escapes to a *closed* answer without the energy exponent.

## 4. The 2-power domain is the WORST case (kills "smoothness helps")

Uncertainty-principle view: RS on `μ_n` = band-limited (`≤k` low frequencies) signals; a pairwise
difference is `k`-sparse in frequency and `(n−a)`-sparse in time. For **prime** `n`, Tao's
uncertainty (`supp_time + supp_freq ≥ n+1`) would forbid dense coincidences — but `n = 2^μ` is the
**worst** order: subgroup indicators are simultaneously sparse in time and frequency, so the densest
coincidence configurations (coset/subset-sum structures — the in-tree census halo,
`SubsetSumHaloEnergy`) are exactly the 2-power obstructions. **"Smooth/2-power helps" is false**; the
2-power structure *maximizes* the energy-type sub-structure. The only genuinely favorable feature is
`n ≪ √q` (rare coset collisions), which places us in the `E(μ_n) ≈ n^{22/9}` regime — still above
`n²`.

## 5. No 2026 paper moves the exponent (checked this session)
- **Kalmynin 2026 / Kim–Yip–Yoo (2602.20919), Cochrane (2602.04111):** breakthroughs on additive
  *decompositions* (`G=A+B ⇒ |G|` a perfect square, `|A|=|B|=√|G|`; subgroups aren't GAPs). These are
  *qualitative* (no clean additive structure) and **give no new energy exponent**; Hanson–Petridis
  `|A||B| ≤ |G|+|(−A)∩B|` is a sumset-confinement L∞ bound, not the L² energy.
- **Kumar–Ron-Zewi (2603.03841):** LD survey; explicit-RS beyond-Johnson list bounds remain at the
  classical wall.
- **Hegyvári (2602.01781):** energy *distribution*, not the subgroup exponent.

## 6. Honest conjecture ledger (rubric: novelty / insight / proximity / feasibility)
| candidate | nov | ins | prox | feas | status |
|---|---|---|---|---|---|
| `δ*(RS[μ_n,k],ε*)` = closed fn of `E(μ_n)` | 5 | 8 | 10 | 2 | **open**: not closed (defers to the energy exponent) |
| tight LD⇒MCA for `n≪|F|` smooth RS | 8 | 8 | 8 | 4 | unblocked by Thm 5.4 but **= the triple-coincidence/energy step** (§3) |
| face (v) curve-irreducibility radius | 9 | 9 | 8 | 4 | new geometric form, but its crossover **= §3 energy** |

**No candidate is ≥9 on `feasibility`/closedness:** every one terminates at the triple-coincidence
control = `E(μ_n)=n^{2+o(1)}`, the 25-year-open exponent, which no acquired result (incl. the 2026
breakthroughs) closes. Per the honesty contract this is recorded as the genuine open core, **not**
fabricated as solved. The contribution this session is the *proof of collapse*: a single elementary
lens (Fisher → Johnson; `√`-loss → Johnson; window → triple coincidences → energy) showing the prize
is **exactly** the smooth-subgroup additive-energy exponent, with the 2-power case being the
hardest, and pinpointing the triple-coincidence step as the *only* place new math can enter.
