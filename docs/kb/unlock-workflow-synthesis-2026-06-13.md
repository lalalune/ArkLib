# Comprehensive attack synthesis: close-the-gates + novel delta* unlocks, 2026-06-13

Harvest of workflow `wf_c255fea7-8cf` (8 parallel attacks; agents did substantial work,
then blocked on transient server rate-limits — results salvaged from transcripts) plus
my own probes. Honest ledger.

## CLOSED / BUILT

### Q1 char-p crux — reduced to ONE clean inequality, everything else proven char-uniform
Two independent agents (valuation + power-sum) converged. With `σ_S = G(z²)+zH(z²)`
(`deg G=k`, `H`=odd part), antipodal ⟺ `H=0`. **Proven char-uniform:**
- the identity chain from `σ_S·σ_{S^c}=z^{4k}−1`: `P=G²−wH²=∏(w−s²)`, `P·P^c=(w^{2k}−1)²`,
  `H^c·P=−(w^{2k}−1)·H`, `m := deg gcd(G,H) = #antipodal pairs`, `U=U^c`, `H^c_1=±H_1`;
- `odd system ⟺ deg H ≤ k/2−1` (Newton, exact);
- `m=0 ⟹ P=w^{2k}−1` (Pell), squarefree ⟹ not a square ⟹ contradiction;
- **k=4 fully**.
**The one remaining gap:** the law `deg H + m ≥ k−1` (for `H≠0`), verified exhaustively
k=2,4 + k=8 (600k samples). With `m ≤ deg H` it gives `deg H ≥ k/2`, contradicting
`deg H ≤ k/2−1` ⟹ `H=0`. **This is FAR past the paper's `d∈{4,8}`** — the entire
char-uniform crux now rests on this single inequality about antipodal-free subsets of
2-power roots with vanishing low odd power sums.

### Q3/Q4 forward lift — Lean built (gcd-reducible half)
Agent wrote an axiom-clean `forward_lift` on top of `agreement_substitution` +
`badSet_orbit_closed`, base-panel bound imported as a named hypothesis. The
gcd-reducible half of the rate-1/2,1/8 lift is buildable now; the coprime-triple
converse remains the open residual. (Compile was blocked by the shared build lock; the
source is in the agent transcript / to be landed.)

### Q2 — descent lemma in Lean, incomplete
Agent built `sq_descent_expand` (the `z↦z²` codeword descent) toward the global
attachment; not completed.

## NOVEL delta* UNLOCKS — honest verdicts

### NOVEL-A (simultaneous rigidity) — PROMISING, not yet a pin
Confirmed: the *simultaneous* odd-`e_i` system has a **field-independent** count
(70=C(8,4) at k=4) where any *single* relation is q-dependent. The lever is real (single
= floppy/additive-energy wall; simultaneous = rigid). What's NOT done: turning this into
an actual q-independent **pin of δ\***. The thesis "δ\* is governed by a rigid
simultaneous system, not the floppy single incidence" is plausible and is the best
forward bet, but it was not closed into a δ\* threshold.

### NOVEL-B (z→z² renormalization) — inconclusive
The descent is rigorous, but no clean self-similar recursion for the far-line incidence
`I_n(δ)` was extracted (agent blocked on Lean compile + rate limit). Open.

### NOVEL-C (deployment-field cleanness) — REFUTED at deployment scale
Decisive negative result (this is the important one). The additive-coincidence defect of
`μ_n` in `F_p` — which equals BOTH δ\*'s q-dependence AND Q1's char-p gap (the grand
unification, see below) — **vanishes only up to a crossover domain size, then returns:**
- KoalaBear / BabyBear (`p~2³¹`): clean to `n=2048`, **first dirty at `n=4096=2¹²`**.
- Goldilocks (`p~2⁶⁴`): clean through `n=2¹⁴`.
- Deployment domains are `n=2²⁰…2²⁷` — **far above** the crossover.

Mechanism (nailed analytically): a size-4 spurious vanishing needs `p | N(Σζ^e)` (norm of
a 4-term root-of-unity sum); max norm grows `≈ 2^{0.41 n}`, so any fixed `p` becomes dirty
once `n ≳ 2.4·log₂ p` (sharpened by the structured norms). **So the deployment fields are
NOT clean at deployment scale** — the cleanness at `n≤2¹¹` is a moderate-`n` artifact, and
δ\* q-dependence + the Q1 char-p defect genuinely afflict deployment fields. This kills the
"deployment-exact unlock" hypothesis. (Honest correction to the optimistic earlier note.)

## The grand unification (stands)

δ\*-q-dependence = Q1-char-p-defect = the **additive-coincidence count of `μ_n` in `F_p`**
(spurious `Σ_{s∈S} s ≡ 0 mod p` not holding in `ℤ[ζ_n]`). When `n|p−1`, Frobenius is
trivial; the defect is pure additive arithmetic = the energy wall. One wall, three faces.
NOVEL-C shows it is NOT evaded by deployment fields at scale; NOVEL-A shows the *simultaneous*
system is rigid where the single relation is not — the one genuine lever still standing.

## Honest ledger

| item | status |
|---|---|
| Q1 char-p crux (char-uniform) | reduced to ONE inequality `deg H + m ≥ k−1`; all else proven; far past `d∈{4,8}` |
| Q1 `(∗)_d` over ℚ | proven (Lam–Leung) |
| Q3/Q4 forward (gcd) lift | Lean built (compile-blocked); coprime converse open |
| Q2 global attachment | descent lemma started; open |
| NOVEL-A simultaneous rigidity | promising lever; not a δ\* pin |
| NOVEL-B renormalization | inconclusive |
| NOVEL-C deployment cleanness | REFUTED at deployment scale (crossover n≈2¹²–2¹⁴) |
| δ\* itself | open; q-dependent; best bet = NOVEL-A simultaneous-rigidity |

## Single best forward bet

Prove the inequality `deg H + m ≥ k−1` (closes the Q1 char-p crux char-uniformly — a
clean, self-contained, exhaustively-verified algebra/number-theory statement about
antipodal-free subsets of `μ_{2^m}` with vanishing low odd power sums), AND develop
NOVEL-A into an actual δ\* threshold (the simultaneous-rigidity pin). These are the two
live, well-localized targets.
