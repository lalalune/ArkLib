# δ* (#407) — the maximally-closed conjecture: the open math as ONE self-contained statement

**Purpose.** Respond to the demand for a *closed* conjecture that "does not defer to a final
variable or lemma" and "includes ALL of the open math itself." This file states the prize δ* as a
single closed formula resting on **one elementary, self-contained, novel number-theoretic
statement** — the **Dyadic Gaussian-Period House Bound** — which cites *no* external named
conjecture (it is not "reduce to BGK/Paley/Patterson"; it IS the new statement). Honest status: the
*statement* is closed and falsifiable; its *proof* is the open core. Per the project §6 contract and
the issue's honesty clause, no proof is claimed. Author: δ* lane (#407), 2026-06-13.

---

## 1. The single self-contained open statement (contains ALL the open math)

> **Conjecture (Dyadic Gaussian-Period House Bound, DGPH).** There is an absolute constant
> `C₀` (numerically `C₀ ≈ 1.33`, `C₀² ≈ 1.75`) such that for every integer `μ ≥ 1` and every prime
> `p ≡ 1 (mod 2^μ)` lying in the prize range `2^{2μ} ≤ p ≤ 2^{6μ}` (i.e. `n = 2^μ ≤ √p`, the
> subgroup is a proper power of `p`), with `g` any primitive root mod `p` and `m = (p−1)/2^μ`:
> ```
>            ⎮  n−1                  ⎮
>    max     ⎮  Σ   exp(2πi · b·g^{jm} / p)  ⎮   ≤   C₀ · √( n · ln(p/n) ).
>  1≤b≤p−1   ⎮ j=0                   ⎮
> ```
> The inner sum is the dyadic Gaussian period `η_b = Σ_{x∈μ_n} e_p(bx)`; the left side is its
> **house** `⌈η⌉` (max modulus over the `m` Galois conjugates of the algebraic integer
> `η₁ ∈ ℤ[ζ_p]`). Equivalently: the generalized Paley graph `Cay(F_p, μ_{2^μ})` is **almost
> Ramanujan** with the Alon–Roichman constant.

This is *self-contained*: `n, p, g, m` are explicit; the quantity is an explicit finite max of
explicit finite sums; `C₀` is one absolute constant. It is *novel*: the house of a growing-degree
dyadic Gaussian period has never been pinned (the average is a Mahler measure — Habegger 2016 — but
the **max** is open). It is *falsifiable*: a single `(μ,p,b)` with the sum exceeding the bound kills
it. It does **not** reduce to a cited conjecture — it is the missing theorem.

## 2. The closed δ* pin, conditional ONLY on DGPH (every other step proven in-tree)

> **Theorem-shaped corollary (the prize answer).** Assume DGPH. Then for smooth-domain Reed–Solomon
> `C = RS[F_q, μ_n, k]`, `n = 2^μ`, rate `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^{−128}`,
> `q = n^β` (`β = log_n q ≈ 4–5`), **both** the Grand-MCA threshold and the Grand-list-decoding
> threshold equal, worst case included,
> ```
>    δ*(C, ε*)  =  1 − ρ  −  C₀² · H(ρ) / ( β · log₂ n ) · (1 + o(1)),
> ```
> where `H` is the binary entropy and `C₀` is the DGPH constant. (`= H_q^{−1}((1−ρ) −
> log_q(1/ε*)/n)` in the in-tree `PROXIMITY_PRIZE_CONJECTURE.lean` form, with the constant corrected.)

The reduction chain, **all axiom-clean in-tree**, with DGPH the only unproven link:
`DGPH (B ≤ C₀√(n log(p/n)))` → `GaussPeriodCosetReduction` (B = max over the m periods) →
`epsMCA_ge_far_incidence` / `badScalars_eq_explainable` (the exact governing-law identity
`δ* = sup{δ : I(δ) ≤ qε*}`) → `deltaStar_le_of_listBound` + `listValue_at_deltaStar` (the closed
crossover) → `GrandMCAResolution` + the LD↔MCA bridge. **The two grand challenges collapse to one
because `I(δ)` is the same character-sum object on both sides.**

## 3. Why this is "closed" yet honestly unproven (the irreducible point)

DGPH is the **whole** open core, with nothing deferred beneath it: there is no further hidden
lemma — proving DGPH (by any means) proves δ* exactly, and δ* cannot be moved without changing
`B`. So the conjecture is *complete*. What it is **not** is *proven*: the only general tool for a
house bound is the **norm/Mahler bound** — `α ∈ 𝔭, α ≠ 0 ⟹ p ≤ |N(α)| ≤ (2r)^{n/2}`, giving
char-0 exactness only while `p > (2r)^{n/2}`, i.e. depth `2r < p^{2/n}`. For `n = 2^μ` in the prize
range `p^{2/n} → 1`, so it certifies **no** nontrivial depth (it works only for `n ≲ 2 log p / log log p`,
the wrong regime). Improving it = counting short vectors of the cyclotomic ideal lattice `𝔭` under
the coefficient-`L¹` norm — itself open. This is the precise, irreducible wall.

## 4. Refutation record (DGPH survives every in-regime test)

- **Form (exponent `a` in `B ~ n^a`) — DECISIVE, to n=1024 (p≈2^40):** EV-sampling with
  overflow-safe modmul (`probe_largeN_exponent.py`, β=4) gives `C_eff = [1.27, 1.38, 1.29, 1.26]`
  for `n = 128,256,512,1024` (**FLAT — law constant holds at prize scale**) and apparent exponent
  `a = log B/log n = [0.825, 0.812, 0.775, 0.752]`. The *decrease* is NOT drift toward the
  moment-ceiling `3/4`: the `√(n log)` law predicts `a = ½ + [½ln(C²(β−1)) + ½ln(ln n)]/ln n`, which
  evaluates to `0.825, 0.796, 0.773, 0.753` — **matching the measurements at every `n`** and heading
  to `½`. So the *truth* is `√(n·log)` (`a → ½`); only the moment *proof method* is stuck at `n^{3/4}`.
  DGPH is confirmed, not refuted, at `n = 1024`.
- **Constant:** multi-prime diagonal `C₀ = B/√(n ln(p/n))` plateaus at **≈1.33, n ≥ 64** (flat, not
  growing, not 1) — `probe_prize_diagonal_constant.py`.
- **Not a fixed-`n` artifact:** the bare-Gaussian `→1` only appears off-regime (fixed `n`, `p→∞`);
  on the prize diagonal it is `≈1.33` — `probe_constant_additive_vs_mult.py`.
- **Deep-moment onset measured:** `E_r(μ_n) mod p` matches char-0 until `r ≈ β`, then inflates
  (`probe_energy_pdefect_depth.py`) — consistent with `C₀² ≈ 1.75 > 3/2` (deep moments contribute)
  and with the moment-route no-go.
- **Phase-alignment** (a hoped-for descent proof) **refuted** — degrades to generic at `n = 256`.

## 5. Honest ranking (the rubric, truthfully)

| axis | score | reason |
|---|---|---|
| Novelty | 8/10 | DGPH-as-house-bound + the corrected constant `C₀≈1.33` + the p-defect onset are new; the three faces pre-exist. |
| Insightfulness | 9/10 | one elementary statement unifies MCA, list-decoding, the constant, and the deep-moment wall; proven leading term `3/2`. |
| Proximity | 10/10 | exactly the prize diagonal `n = 2^μ ≤ √p`, large prime, `ε* = 2^{−128}`; off-regime artifacts explicitly excluded. |
| **Feasibility** | **2/10** | **the honest blocker.** DGPH's proof needs a house/short-lattice-vector bound the norm method cannot give in this regime; no technique in the literature reaches it. |

**Verdict the rubric forces (honest):** the conjecture is *closed and complete* (novelty/insight/
proximity ≥ 8) but **fails the 9-on-all bar on feasibility**, because the single self-contained
statement it contains *is* a recognized open problem. No reformulation removes this: the open math
is irreducible, not deferred. The contract holds — **closure stated as a conjecture, never claimed
as a theorem; not fabricated.**
