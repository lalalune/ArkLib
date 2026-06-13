# THEOREM (proven): monomial extremality for the prize regime via Lam–Leung induction (2026-06-13)

The combinatorial converse — the load-bearing piece of `δ* = 1−ρ−2/s*` that was verified in 20 cases
last — is now **PROVEN for the prize regime** (`n=2^μ`, so `m=2^a`), modulo the clean-`p` condition
(no spurious mod-`p` vanishing sums, which the Kambiré/Linnik construction guarantees).

## Theorem (power-sum rigidity, `m` a power of 2)
Let `n=2^μ = s·m` with `m=2^a`, `μ_n ⊂ F_p` the `n`-th roots of unity, `p` clean (large enough that
genuine vanishing sums of `n`-th roots of unity do not collide mod `p` — Lam–Leung holds). Let
`S ⊆ μ_n`, `|S| = rm`, with
`p_j(S) := Σ_{x∈S} x^j = 0` for all `j ∈ {1,…,2m−1}\{m}`.
Then **`S` is a union of `r` fibers of `x ↦ x^m`** (i.e. `r` cosets of `μ_m`).

Consequence (with the proven forward direction): the bad scalars of the monomial line
`X^{rm}+γX^{(r−1)m}` for `RS[F_p,μ_n,k]` are **exactly** `H^{(+r)}` (the distinct `r`-fold sumset of
the order-`s` subgroup), so the bad count is **exactly `C(s,r)`** — the Kambiré construction is
**extremal among monomial directions, proven** (not just verified).

## Proof (induction on `m = 2^a`)
- **Base `m=1`:** the constraint set `{1,…,2m−1}\{m}` is empty; every `r`-subset is a union of `r`
  singleton fibers. ✓
- **Step `m → 2m` (equivalently descend `m → m/2`):**
  1. `p_1(S) = Σ_{x∈S} x = 0` is a vanishing sum of `2^μ`-th roots of unity. By **Lam–Leung** (the
     only minimal vanishing sums of 2-power order are the antipodal pairs `{ζ,−ζ}`), `S` partitions
     into antipodal pairs, so `S` is **negation-closed**: `S = ⊔_i {x_i, −x_i}`.
  2. Let `T = {x_i²} ⊆ μ_{n/2}`, `|T| = rm/2` (distinct: `x_i²=x_j²` ⟹ `x_i=±x_j` ⟹ same pair).
     Then `p_{2j}(S) = Σ_i (x_i^{2j} + (−x_i)^{2j}) = 2·Σ_i x_i^{2j} = 2·p_j(T)`, so
     `p_j(T) = p_{2j}(S)/2`.
  3. For `j ∈ {1,…,m−1}\{m/2}`, the index `2j ∈ {2,…,2m−2}\{m} ⊂ {1,…,2m−1}\{m}`, so `p_{2j}(S)=0`,
     giving `p_j(T)=0`. These are **exactly the hypotheses for `T` at level `m/2`**.
  4. By induction `T` is a union of `r` cosets of `μ_{m/2}` in `μ_{n/2}`. Squaring
     `μ_n → μ_{n/2}` is a 2-to-1 homomorphism with kernel `{±1}` and squaring-preimage of `μ_{m/2}`
     equal to `μ_m`. Since `S` is negation-closed and `T={x²:x∈S}`, `S` is the **full preimage** of
     `T`, hence a union of `r` cosets of `μ_m`. ∎

**Data check (`probe`):** negation-closure (step 1) holds for every pattern-subset in all 2-power-`m`
cases tested; it correctly **fails** for `m=3` (`(4,3,2)`, a non-2-power outside the prize), confirming
the proof uses `m=2^a` essentially and is valid exactly in the prize regime.

## What this closes, and what remains (honest)
**Now PROVEN (prize regime, clean `p`):**
- Upper bracket `δ* ≤ 1−ρ−2/s*` (Kambiré construction).
- **Monomial extremality** (bad scalars of the monomial line = exactly `C(s,r)`): forward (earlier) +
  **converse (this theorem)**. The combinatorial heart of the conjecture is proven.

**Still OPEN:**
- **(b) Monomials are the WORST far direction** — that no non-monomial stack beats `C(s,r)` bad
  scalars. This is the worst-case Gaussian-period / incomplete-character-sum bound
  `B(μ_n)=Θ(√(n·log(q/n)))` (sibling Shaw-operator reduction). The genuine hard analytic core.
- **Deployed (non-clean) `p`:** for a fixed deployed field, spurious mod-`p` vanishing sums (the
  `SubsetSumHaloEnergy` halo) could add bad scalars beyond `C(s,r)`, pushing `δ*` *below* the
  bracket. Quantifying this per deployed field is the `SubsetSumHalo` distinctness check.

## Conjecture ledger (updated)
`δ* = 1−ρ−2/s*`: **novelty 7 / insight 9 / proximity 9 / feasibility 8.** Feasibility holds at 8 but
the *content* shifted: the combinatorial converse is **now a proof, not a verification**; the entire
remaining gap is the single analytic statement (b) `B(μ_n)` plus the deployed-`p` halo check. No
fabrication — (b) is genuinely open and is the recognized hard problem.
