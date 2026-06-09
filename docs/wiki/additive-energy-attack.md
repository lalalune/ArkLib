# The additive-energy attack on the Proximity Prize (#232)

This page documents the machine-checked reduction chain that takes the Ethereum Proximity Prize
(issue #232, [ABF26]) down to a single named, decidable-per-instance open hypothesis on the
**additive energy of the smooth `2^k`-multiplicative subgroup**. It is a durable reference so future
agents target the genuine open root rather than re-deriving the (now complete) supporting chain.

> Scope reminder: the prize itself is **open research** and **not closeable by this repo** (see the
> issue body and `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`). Everything
> below is honest formalization of the *reduction*; the open root is named, not solved.

## The chain (all axiom-clean: `propext, Classical.choice, Quot.sound`)

```
prize (pin δ* in (1−√ρ, 1−ρ))
  → MCA / ε_mca bad-event count                    (#141 surfaces)
  → subset-sum concentration of the smooth subgroup G ⊆ F_q^×
  → coordinate descent down the 2-power subgroup tower
  → 2nd / 4th Gauss-sum moments  (∑_b ‖η_b‖⁴ = q · E(G))
  → additive energy  E(G) = #{(a,b,c,d) ∈ G⁴ : a+b = c+d}
  → [OPEN] is E(G) minimal (≈ char-0 value) for the explicit 2^k-subgroup at ε*=2^−128?
```

## Where each step lives

| Step | File(s) | Key result |
|---|---|---|
| Subgroup-tower descent (general `d`) | `SubgroupPowerHalvingGeneral` | `image_pow_eq_quotient`: `(μ_{dm}).image(·^d) = μ_m` (index-`d` subgroup), any `d,m≥1`. Special cases: `SubgroupSquaresHalvingRecursion` (d=2), `SubgroupQuarticHalvingRecursion` (d=4). |
| Coordinate descent (Finset model) | `SubsetSumQuarticDescent` (d=4), `SubsetSumSquaringBijection` (d=2) | surviving symmetric coordinate `∑x^d` reduces to a subset-sum over the `d`-th-power image. |
| Gauss-sum moments | `SubgroupGaussSum{Second,Fourth}Moment` | `subgroup_gaussSum_fourthMoment : ∑_b ‖η_b‖⁴ = q · addEnergy G`; heavy-frequency / no-go's in `ListSizeMoments`, `MomentCollisionTower`, `JohnsonFourthMomentNoGo`. |
| Energy bound from representations | `AdditiveEnergyRepBound` | `additiveEnergy_le_three_of_repTwo : repCount ≤ 2 ⟹ E ≤ 3|G|²`. `repCount ≤ 2` is **false** over small `F_q` (`SubgroupRepCountFiniteFieldCounterexample`). |
| **Sharp energy (equality)** | `AdditiveEnergySidonModNeg` | `additiveEnergy_eq_of_sidonModNeg : E(G) = 3|G|² − 3|G| = 3|G|(|G|−1)` for any **Sidon-mod-negation** set (negation-closed; only trivial/zero-sum additive coincidences). Sharpens the `≤ 3|G|²` bound by exactly `3|G|`. |
| Definition bridge | `AdditiveEnergyBridge` | `additiveEnergy_eq_addEnergy`: the rep-count `additiveEnergy` (above) equals the quadruple-count `SubgroupGaussSumFourthMoment.addEnergy`; hence `addEnergy = 3|G|(|G|−1)` for Sidon-mod-neg, feeding the fourth-moment identity. |
| Concrete data / validation | `SubgroupAdditiveEnergyTowerF17`, `SubgroupAdditiveEnergyFermat257`, `SubgroupAdditiveEnergyFermat65537`, `AdditiveEnergyFullGroupClosedForm`, `SidonModNegValidationFermat257` | exact `decide` energies; general `E(F_p^×) = (p−1)²+(p−1)(p−2)²`; end-to-end theorem validation; `SidonModNeg` threshold located. |

## The two load-bearing empirical facts (verified by `decide`)

1. **Prize-regime anti-concentration.** For a *small* subgroup in a *large* field (`|G| ≪ q`, the
   deployed regime), the additive energy equals the characteristic-0 value: `E(order-8) = 168 =
   3·8·7` for `q ∈ {257, 65537, …}` (`q`-independent). The `repCount = 3 > 2` "counterexample" is a
   **small-`q` artifact** (`q ~ |G|`), not the prize regime.
2. **The crossover is field-arithmetic-dependent — no clean law in `q`.** The order at which
   `E > 3|G|²` first occurs is `~8, ~16, ~32` for `q = 2^4+1, 2^8+1, 2^16+1`; across 15 fields it
   fits neither `√q` nor `2·log₂q`. (A `√q` claim was posted and **retracted** — see #232 comments;
   recorded here so it is not re-attempted.)

## The open root

Whether `SidonModNeg` holds — equivalently, whether `E(G) = 3|G|(|G|−1)` (minimal/anti-concentrated)
— for the **explicit** smooth `2^k`-subgroup at the prize threshold `ε* = 2^{−128}` as `|G|, q → ∞`,
is the **field-arithmetic-dependent Weil / Heath-Brown–Konyagin sum-product** input. It is decidable
per concrete instance but open in the asymptotic prize regime. This is the "new mathematics" the prize
requires; the formalization side of this attack is otherwise complete.

## Lessons for future agents

- The proximity frontier is driven by a fast multi-agent swarm pushing to `main` (~1 file/min). Solo
  value is reliably **(a) fix fresh build breakage** and **(b) land the brick one step past the
  swarm**, then verify against `upstream/main` *before* building — a `git ls-tree`/grep check is not
  enough (the swarm sometimes pushes red commits).
- Apply the apophenia gate hard: assert a scaling law only after many witnesses (the `√q` retraction).
- `decide` over `∀ a ∈ G` for `G : Finset (ZMod p)` blows up to `p^k` if the def is unfolded into a
  Fintype quantifier; use `Finset.decidableBAll` (keep `G` a Finset) or `fin_cases`.

## References
- [ABF26] Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*, ePrint 2026/680.
- Issue #232; `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`.
