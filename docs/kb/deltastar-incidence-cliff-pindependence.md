# δ* p-independence via the incidence CLIFF — and the precise B5 answer (#407)

**Status: genuine structural finding, n=16 full + n=32 cliff confirmed; NOT a closure; one caveat + the large-n question open.**

## The mechanism: an incidence cliff at the over/under-determined boundary

The exact far-line incidence `I(a,b;r)` (number of γ with the line `x^a+γx^b` within distance r of RS[μ_n,k])
has a sharp CLIFF as a function of the witness size `s = n−r` relative to `k`:

| regime | conditions on γ per witness | incidence | p-dependence |
|---|---|---|---|
| **over-determined** `s−k ≥ 2` | ≥2 (over-constrained) | `O(1)`–small (structured) | **p-INDEPENDENT** |
| **critically/under-determined** `s−k ≤ 1` | ≤1 | `Θ(C(n,s)) ~ Θ(q)` (saturated) | **p-DEPENDENT** |

Verified at n=32, k=4 (ρ=1/8), 3 primes p∈{200003,500009,1000003}:
- `s=6` (s−k=2, over-determined): maxI = **[1, 1, 1]** — p-independent.
- `s=5` (s−k=1, under-determined): maxI = **[125408, 163872, 179872]** — p-DEPENDENT, ~0.6q.

The incidence jumps from `O(1)` to `~10^5` across one step in s. (n=16 analog: over-determined s=6 gave 89,
p-independent; the cliff is the same.)

## Why δ* is p-INDEPENDENT even though the count is p-DEPENDENT (the key subtlety)

`δ* = sup{δ : maxI(⌊δn⌋) ≤ budget}`, budget `= q·ε* ~ n`. δ* is a THRESHOLD, not the count. p-independence of
δ* requires only that `sign(I(r) − budget)` is the same across primes at each r — NOT that I(r) itself is
p-independent. Because the prize **budget ~n falls in the cliff GAP** (`O(1) ≪ n ≪ Θ(q)`):
- at the over-determined radius, `I = O(1) ≤ budget` for ALL primes (uniformly good);
- at the under-determined radius, `I = Θ(q) > budget` for ALL primes (uniformly bad, despite differing counts).

So **δ* is pinned p-independently by the cliff location**, even though the under-determined count carries char-p
info. The cliff does the work the BGK char-sum max was thought to do.

## The precise answer to dossier B5 ("CensusDomination = E(μ_n) 2nd-order, or deep?")

Both lanes are real and DIFFERENT, reconciled by the cliff:
- The **count** (CensusDomination / under-determined incidence) is **p-DEPENDENT** — it is NOT a purely
  combinatorial 2nd-order object; it carries the char-p / additive-energy information (consistent with it being
  Shkredov's E(μ_n) at the count level).
- The **threshold δ*** (the prize quantity) is **p-INDEPENDENT** — it decouples from the p-dependent count (and
  hence from the BGK char-sum max) because the budget sits in the incidence cliff gap.
So the `δ* = BGK` reduction IS lossy (as the in-tree loss-web marks `I→M` √-lossy): δ* is the cliff location,
a combinatorial quantity, NOT the p-dependent BGK period max.

## Caveats / what stays open (no overclaim)

1. **Under-sampled directions at n=32:** the over-determined maxI=[1,1,1] used only 4 monomial directions. The
   TRUE max over all far directions at the over-determined radius could be larger; if it straddles the budget
   across primes, δ* could become p-dependent there. Needs the full-direction search (the decoupling army's job).
2. **Large-n cliff-vs-budget:** does the budget ~n ALWAYS fall in the cliff gap as n→2^30? The gap is
   `[O(1), Θ(C(n,k+1))]`; `C(n,k+1) ≫ n` for the prize, so the gap is wide — but the exact over-determined
   incidence growth vs n must be mapped to be sure the binding stays over-determined (p-indep) and never lands
   exactly at the cliff edge (where p-dependence could enter). This is the precise form of the ">2^12 crossover".
3. If the binding ever lands AT the cliff edge (`s−k=1` exactly with I straddling budget across primes), δ*
   becomes p-dependent and reduces to the wall there.

**Net:** δ* p-independence is REAL and now has a mechanism (the incidence cliff with budget-in-the-gap), giving
a precise B5 answer (count p-dependent, threshold p-independent). The remaining open piece is whether the binding
stays strictly inside the over-determined regime for all prize n — a sharp, checkable question, not the diffuse
BGK wall. Probe: `probe_407_n32_incidence_cliff.py`.
