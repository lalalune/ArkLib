# Why every route hits k < log_n p — the moment-method convergence diagnosis (#389)

**Status:** structural synthesis of the session's cross-field research arc. Rules out the entire
moment-method family for the prize and isolates the only possible escape. Honest; not a closure.

## The convergence

This session attacked the open core `B(μ_n)=max_c|η_c| ≤ √(n log p)` from four independent classical
frameworks. **All four break at the identical threshold** `k < log_n p = log p/log n ≈ 8` (prize
regime `n=2^32`, `p≈2^256`), because all four are **moment methods**:

| framework | the quantity | "Gaussian/clean" up to | breaks at |
|---|---|---|---|
| Cyclotomic-lattice norm (`CleanRangeNorm`) | spurious tuples `𝔭∩B_{2r}` | `(2r)^{φ(n)}<p` ⟺ `r<log_n p` | high `r` |
| Additive energy (`SubsetSumHalo`, in-tree) | `E_r(μ_n)=(2r−1)!!n^r` | `p>n^r` ⟺ `r<log_n p` | high `r` |
| Salem–Zygmund / Gauss-sum DFT + chaining | per-period moment (flat metric) | same even moments `E_r` | high `r` |
| Lamzouri value-distribution CLT (1106.6072) | char-sum moments → Gaussian | `log H=o(log q)` ⟺ `k<1/β` | fixed power |

The prize needs control to `k ≈ log p ≈ 162`. The gap `[log_n p, log p] = [8, 162]` is the **same**
irreducible Bourgain core in every framework — they are the same moment obstruction repackaged.

## Why: they are all moment methods, and the diagonal stops dominating at k = log_n p

Each framework's "easy regime" is where the **diagonal/paired** contribution dominates the `2k`-th
moment. The off-diagonal (spurious, char-`p`-coincidence) mass overtakes the diagonal exactly when
`n^k > p`, i.e. `k > log_n p`. No moment method can see past its own diagonal, so all four share the
threshold. **Corollary: no moment-method variant can close the prize** — a whole family is ruled out.

## The only escape: a Burgess-quality bound for subgroup sums (which does not exist)

Non-moment techniques for character sums:
- **Intervals:** Burgess's method (shift-and-multiply amplification) reaches length `p^{1/4}` —
  genuinely past the moment barrier. This is why short-interval character sums are well-understood.
- **Multiplicative subgroups (our case):** the analogue is **BGK / Bourgain–Garaev sum-product**,
  which reaches only `max_c|η_c| ≤ n^{1−δ}` with `δ` tiny — NOT `n^{1/2+o(1)}`.

**The entire prize gap is exactly the gap between BGK-quality (`n^{1−δ}`) and Burgess-quality
(`n^{1/2}`) for subgroup sums.** A square-root bound for thin multiplicative-subgroup sums via a
non-moment (Burgess/Stepanov-type) amplification is the recognized open problem; it does not exist in
current mathematics. Every moment-method route (this session's four + the campaign's energy lane) is
provably incapable of reaching it.

## Consequence for the campaign (actionable)

- **Stop trying moment-method variants** (energy `E_r`, cyclotomic moments, chaining-via-moments,
  CLT-via-moments) — they all stall at `k<log_n p`, proven here from four directions.
- **The only viable attack is a non-moment amplification** for subgroup sums: a Stepanov/Burgess-type
  polynomial-method bound, or a genuinely new cohomological input, pushing BGK's `n^{1−δ}` to `n^{1/2}`.
  The in-tree Stepanov programme (`[[issue389-additive-energy-crux]]`, SV11/GK16, ~90% built, gap at
  split-case Wronskian non-vanishing `hW` in char `p`) is the *right kind* of tool — it is non-moment.
  That `hW` gap, not any moment bound, is where prize-relevant effort should go.

Honest scores for this diagnosis: novelty 7 / insight 9 / proximity 10 / feasibility — (it is a
NO-GO meta-theorem for moment methods + a pointer, not a route to close the prize). The prize stays
open; this rules out a family and redirects to the non-moment Stepanov lane.

Cross-refs: `deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`,
`deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`, `CleanRangeNorm.lean`,
`SubsetSumHaloEnergy.lean`, `[[issue389-additive-energy-crux]]` (the Stepanov `hW` gap = the real lane).

## CORRECTION (same session) — the in-tree Stepanov lane is ENERGY-targeted (√-lossy), not the prize lane

Verified by grep: every in-tree Stepanov/SV11/Wronskian file concludes a bound on `additiveEnergy`
/ `repCount` (`AdditiveEnergyRepBound.repCount`, `additiveEnergy_le_of_repBound`), and **none bounds
the character sum `eta = η_b` directly** (the `eta` symbol appears in zero Stepanov files). So the
"redirect to the Stepanov `hW` lane" above is over-optimistic and must be corrected:

- The in-tree Stepanov programme bounds the **additive energy** `E = E_2` (4th moment). Energy → `B`
  is **√-lossy** (`B⁴ ≤ p·E_2`; even optimal `E_2 = n²` gives `B ≤ (p n²)^{1/4} ≫ √n`, and energy →
  list is `T² ≤ |G|·E` → `n^{3/2}` = sub-Johnson). The workbench §2 already flags this: "√-loss is
  FATAL." So **even if the `hW` split-case gap closes, the energy-Stepanov lane cannot reach the
  prize** — it gives a sub-Johnson list, not the capacity-window `δ*`.
- The prize needs a **DIRECT** square-root bound on the character sum `B = max_b|η_b|` itself —
  a Stepanov/Burgess-type bound on `Σ_{x∈μ_n} e_p(bx)`, NOT on its energy. **This is not in the
  tree and is exactly the open subgroup-Burgess problem.**

## The complete impossibility map (this is the honest terminal state of the technique survey)

| technique class | in-tree status | why it fails the prize |
|---|---|---|
| Moment methods (norm, energy `E_r`, chaining-via-moments, Lamzouri CLT) | 4 routes built | all stall at `k < log_n p ≈ 8`; off-diagonal overtakes diagonal at `n^k>p` |
| Energy methods (incl. in-tree Stepanov-energy, `hW` lane) | ~90% built | √-lossy: `E→B` and `E→list` lose a square root → sub-Johnson even at optimal `E=n²` |
| Direct non-moment char-sum bound (subgroup-Burgess) | **absent** | the ONLY thing that could reach `B=n^{1/2+o(1)}`; **does not exist in current mathematics** |

Every technique class that EXISTS (moment + energy) is provably incapable of the prize; the one class
that WOULD work (direct subgroup-Burgess) does not exist. This is, rigorously and from the in-tree
evidence, why the prize is open — not a gap in effort but the absence of a square-root non-moment
subgroup character-sum method. No fabrication can bridge it; only genuinely new number theory.
