# Targeted literature survey of the REDUCED form: anti-concentration of `r`-fold subset sums of `μ_n` mod `p` (2026-06-13)

After the direct attack localized the entire prize to a single gate — the Markov bridge
(`docs/kb/deltastar-DIRECT-ATTACK-markov-mechanism-2026-06-13.md`) needs
`M_r = Σ_{b≠0}η_b^{2r}` clean (`≤ p·(2r−1)!!·n^r·(1+o(1))`) up to `r ≈ c·ln p`, equivalently
**anti-concentration of the `≤c·ln p`-fold subset sums of `μ_n` mod `p`** = BCHKS Conjecture 1.12 —
this note surveys the literature on *exactly that reduced object* (the user's "research what it
reduces to / check congruence"). Verdict: **the object is recognized and studied on both flanks, but
the prize band is the genuine open gap between them. No closure available; congruent with my scaffold.**

## The three relevant flanks (all fetched, `~/papers/arklib/_new/user5-*`)

1. **Jain–Sah–Sawhney, "Anticoncentration vs the Number of Subset Sums" (arXiv 2101.07726, Adv. Comb. 2021).**
   Right *shape*: bounds `|R(w⃗)| = #{Σ ξ_i w_i : ξ∈{0,1}^n}` given Lévy concentration `ρ(w⃗)≥exp(−εn)`,
   proving `|R(w⃗)| ≤ exp(C√ε·n)` (their `δ(ε)=O(√ε)`). But ambient is **real/integer** `w⃗` — no mod-`p`
   reduction, no multiplicative structure. The "subset sums anti-concentrate unless low-rank-GAP
   structured" theme is morally my statement, but the inverse-Littlewood–Offord exceptional-set is
   "too large to rigorously establish" the clean version (their own §1 remark) — i.e. even in the clean
   real setting the *rigorous* sharp form is open. Does **not** transfer to `μ_n` mod `p`.

2. **Hanson–Petridis, "Refined Estimates Concerning Sumsets Contained in the Roots of Unity"
   (arXiv 1905.09134, PLMS 2021).** The `r=2`/`L∞` structural flank: `|A||B| ≤ |G| + |(−A)∩B|` for
   `A+B ⊆ μ_n`, giving Paley clique `≤ √(p/2)+1` and "decompositions are co-Sidon." This is **exactly
   the order-2 bound I already have tightly** via Lam–Leung (`E₂(μ_n)=3n²−3n` exact in the prize
   regime). Their polynomial method is order-2-bound to the *containment* `A+A⊆μ_n`; it does **not**
   climb to the `r`-fold moment `M_r` for growing `r`.

3. **Erdős-distinct-subset-sums-mod-`N` (arXiv 2308.03748) and subset-sums-of-`Zₙ^×` (2304.14141).**
   Worst-case *generic* sets — `N ≥ 2^n`-type thresholds for ALL `2^n` subsets distinct. My object is a
   **specific geometric sequence** `{g^e}` and only `r`-term (not all-subset) sums, so these are far
   coarser; they bound the wrong (worst-case, all-subset) quantity.

## Why the prize band is the gap between flanks (the honest congruence statement)

- Flank (2) pins `r=2` exactly (and `r≤log_n p` follows by Sidon-`B_r`/pigeonhole — provable, ≈6 for
  the prize). Flank (1) is the `r→n` (all-subset) regime, real-valued, and itself non-rigorous-sharp.
- The bridge needs the **middle band** `r ∈ (log_n p, c·ln p) = (≈6, ≈133)` for the prize, *mod `p`*,
  *for the multiplicative subgroup*. **No surveyed result covers this band.** Stepanov/BGK need
  `n>p^ε`; Weil gives only `√p`; the cyclotomic-norm height bound `p≤(2r)^{2^{k−1}}` has no teeth at
  large `n` (always satisfied) → it is a **counting** problem, not a height problem, exactly as BCHKS
  1.12 states. Szabó 2409.13436 calls the unconditional version "hopeless with current knowledge."

## Conclusion (no new lever, scaffold confirmed)

The reduced form is **genuinely the recognized open conjecture** — congruent with
`issue389-deltastar-proven-scaffold-2026-06-13` and the session master map. The targeted survey
**adds no transferable bound** for the prize band; it confirms the gate is open on both the rigorous
real-valued side (Jain–Sah–Sawhney's own caveat) and the finite-field side (Hanson–Petridis stops at
order 2; Stepanov/Weil insufficient). **Honest status: the prize remains reduced to one named, studied,
open conjecture (BCHKS 1.12), with a PROVEN bridge from it to `δ*`. Not fabricating a closure.**
