# #407 deep-moment literature sweep (2026-06-14): the high-moment depth `r≍log p` is genuinely unaddressed

**Context.** Per the consolidated meta-theorem (#407), the entire open core is char-p validity of the
**deep-moment** bound `(DM_r): q·E_r(μ_n) ≤ m·(2r−1)‼·n^r` at depth `r ≍ log m ≍ log p`, where
`E_r(G) = #{(x_1..x_r,y_1..y_r)∈G^{2r} : Σx=Σy}` is the r-fold additive energy of the multiplicative
subgroup `μ_n ⊂ F_p`. This is the only un-capped route (all second-order methods provably cap at √S).

**Sweep goal.** Find any recent (2024–2026) result bounding `E_r` of a multiplicative subgroup at depth
`r` growing with `log p` (not fixed small r), with sub-Wick / √-cancellation precision.

## Reading list (5 papers, exact object = r-fold subgroup energy / higher convolution moments)

1. **Schoen–Shkredov, "Higher moments of convolutions"** — arXiv:1110.2986. The r-fold energy IS a higher
   moment of convolutions of `1_G`. THE most on-target framework. *Needs full read:* does it cover `r`
   growing (not fixed), and does the bound carry the `(2r−1)‼` Wick constant rather than a crude `|G|^{r+c}`?
   (Abstract only studies "higher moments … generalizing additive energy"; depth-range not in abstract.)
2. **"On the distribution of additive energy revisited"** — arXiv:2602.01781 (Feb 2026, newest). Fourier
   method for energy *distribution* + product-set covering for small-doubling sets. Appears low-moment;
   verify whether the distributional control says anything at high moments.
3. **"On additive irreducibility of multiplicative subgroups"** — arXiv:2504.10202 (Apr 2025, Stepanov via
   Hanson–Petridis). Result: `A−A=μ_d∪{0} ⟹ d∈{2,6}`; Sárközy QR-decomposition. STRUCTURAL/qualitative,
   not quantitative `E_r`. Relevant to the in-tree Stepanov programme (`[[issue389-additive-energy-CRUX]]`).
4. **Shkredov, "Some new inequalities in additive combinatorics"** — arXiv:1208.2344. Upper bounds for
   additive energy of multiplicative subgroups + the energy↔higher-convolution-moment connection.
5. **"On additive shifts of multiplicative almost-subgroups"** — arXiv:1507.05548 (+ tripling-constant
   1504.04522). `|3Γ| ≫ |Γ|²/log|Γ|`, `E^×(Γ+x) ≪ |Γ|² log|Γ|` — the SOTA low-moment structural bounds.

## Verdict (honest)

**The literature confirms the gap, it does not fill it.** Every located result bounds *low* moments
(`E_2`, `E_3`), proves sum-product / covering, or gives structural (irreducibility) statements — all
"second-order" in the meta-theorem's sense, hence provably capped at the Johnson/√p deficit. **None reaches
the depth `r ≍ log p`** with the sub-Wick precision `(DM_r)` demands. This is *why* the prize is open: the
deep-moment object lives in a regime where current additive-combinatorics technique has no result. The newest
paper (Feb 2026) is still distribution-of-low-energy. The Stepanov/Hanson–Petridis method (the in-tree
programme's tool) gives structure, not the high-moment count.

**Implication for attack:** a closure must come from a genuinely new high-moment technique (or the char-0→char-p
transfer at depth, controlling only the spurious mod-p wrap-around collisions — the `[[issue407-no-excess-count-face]]`
/ T1-boundary observation that excess is 0 until `p~n^{r}`). The additive-combinatorics low-moment toolkit,
even at 2026 SOTA, does not bridge to `r≍log p`. Consistent with `[[issue407-metatheorem-confirmed-airtight]]`.

## SOTA exponent localization (lit search 2026-06-14, decisive)

Fresh search on the EXACT object (subgroup exponential sum exponent). SOTA:
- **di Benedetto–Garaev / arXiv:2401.04756** ("Exponential sums over small subgroups, revisited", Jan 2024):
  `max_a |Σ_{x∈H} e_p(ax)| ≤ H^{1−31/2880+o(1)}` — **only for `H > p^{1/4}`**.
- Limiting case `H ~ p^{1/4}` (Bourgain–Garaev): `H^{1−175/9437184+o(1)}`, exponent gain `≈1.85e−5`.

**DECISIVE localization:** prize is `n=2^μ`, `q=n^β`, `β≈4–5` ⟹ `n = q^{1/β} ≤ q^{1/4}` — AT or BELOW the
`p^{1/4}` threshold, exactly where the di Benedetto power-saving VANISHES and only BGK's *ineffective*
`n^{1−o(1)}` survives. Prize needs exponent `1/2`; SOTA at the prize point is `1 − 1.85e−5`. The gap is a
**full half-power at the single hardest point for every known method.** No 2025–26 breakthrough crosses it.
Reading-list add: arXiv:2401.04756 (latest SOTA), arXiv:2003.06165, arXiv:2401.04756, arXiv:1401.4618 (elementary), arXiv:1809.06837.
**Conclusion:** the "external math to apply" does not yet exist; the wall is unbroken in the literature and
the prize occupies its worst case (`n ≤ p^{1/4}`).
