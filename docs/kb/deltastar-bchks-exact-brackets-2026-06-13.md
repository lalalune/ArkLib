# The EXACT proven δ* brackets, from BCHKS25 (ECCC TR25-169) — read from source (2026-06-13)

Read directly from BCHKS25 (ECCC TR25-169 = ePrint 2025/2055) Tables 1–2, Thm 1.3, Thm 1.13.
This replaces the hand-waved "1−ρ−Θ(1/log n)" with the **exact** constants and clarifies that the
open window has **constant width**, not a `1/log n` sliver.

## 1. Lower bracket (PROVEN, ε*=0 ⟹ ≤ 2^{-128}): δ* ≥ Johnson `1−√ρ`
Table 1, "This work" row: proximity gaps hold for `γ < 1−(1−δ)^{1/2}−η` with proximity loss
**ε*=0** and `a ≥ Θ_δ(n/η)` (improving BCI+20's `Θ(n²/η)` by a factor `n`). Here `δ = 1−ρ` is the
relative minimum distance, so `1−(1−δ)^{1/2} = 1−√ρ` = the **Johnson radius**. So MCA holds (ε*=0,
hence `≤ ε*`) for **all `δ < 1−√ρ`** — the proven floor. (`a=Θ(n/η)` is the per-fold list parameter;
the field-size requirement is `q ≳ a/ε*`.)

## 2. Upper bracket (PROVEN negative): δ* ≤ `(1−ρ) − 1/log₂ n`
Table 2, "This work, δ≈1/2, Mersenne prime q" row:
> at radius `γ = δ − 1/log₂ n` (i.e. `1/log₂ n` below the relative min distance `δ=1−ρ`), the
> proximity loss is **`ε* ≥ 1/(2 log₂ n)`**, with `a = n = q`.

Since `1/(2 log₂ n) ≫ 2^{-128}` (for `n=2^{30}`, `1/(2·30)=1/60`), that radius is **bad for the
prize budget**, so **δ* ≤ (1−ρ) − 1/log₂ n**. For Mersenne `q` this is **unconditional**
(`G=⟨−2⟩` via binary expansions, Remark 7.3); for general 2-adic NTT fields it is conditional on the
subgroup-sumset admissibility **Conj 1.12** (`∃ b≤10 log q` with `|G^{(+b/2)}| ≥ q/10`).

Other unconditional negative rows (Table 2): `δ=15/16, γ=3/4, a=n^{2−o(1)}, ε*=1/8`;
`δ=1−λ_τ, γ=1−4λ_τ, ε*=2λ_τ` (any `τ`, `λ_τ=2^{−(τ+2)}`); and the **list-decoding-radius** row
`γ = LDR(δ)+2/n, a=q/2n, ε*=δ−γ−1/n` — i.e. pushing the gap radius past LDR forces large loss.

## 3. THE WINDOW IS CONSTANT-WIDTH (the honest size of the open problem)
`δ* ∈ ( 1−√ρ , (1−ρ) − 1/log₂ n )`. Width `= (√ρ − ρ) − 1/log₂ n → √ρ − ρ` as `n→∞`:

| ρ | Johnson `1−√ρ` | capacity `1−ρ` | window width `√ρ−ρ` |
|---|---|---|---|
| 1/2 | 0.293 | 0.500 | **0.207** |
| 1/4 | 0.500 | 0.750 | **0.250** |
| 1/8 | 0.646 | 0.875 | **0.229** |
| 1/16 | 0.750 | 0.938 | **0.188** |

So for the four prize rates, `δ*` is pinned only to a window of width **0.19–0.25** — a *large*
constant gap, not a `1/log n` sliver. **Pinning δ* anywhere inside is the open prize**, and the
window does not shrink with `n`. (My earlier `n=16` data with `δ*∈(0.625,0.688)` sat above the
asymptotic window because at `n=16`, `1/log₂n = 1/4` makes the upper bracket collapse onto Johnson —
the window is empty for tiny `n`.)

## 4. What this nails down (accurate, source-grounded)
- The "answer form" `δ* = 1−ρ−Θ(1/log n)` is **only the UPPER bracket**, not the value. The lower
  bracket is the *constant* `1−√ρ`. So the value is somewhere in a width-`(√ρ−ρ)` band.
- The positive side (Thm 1.3) gives the Johnson floor **unconditionally with the improved `a=Θ(n/η)`**
  — the in-tree Hab25/Johnson lane matches this. The prize is entirely the *interior*.
- The upper-bracket negative construction is **gated on Conj 1.12** for 2-adic NTT fields (the prize's
  actual fields); unconditional only for Mersenne `q`. So even the upper bracket for the prize's
  smooth domains is conditional — matching the in-tree `SubsetSumHaloEnergy` framing of Conj 1.12.

## 5. Honest status
This is the precise, source-grounded bracket statement: `δ* ∈ (1−√ρ, 1−ρ−1/log₂ n)`, a constant-width
open window at each of the four prize rates; lower bracket proven (Johnson, ε*=0), upper bracket proven
for Mersenne / conditional-on-Conj-1.12 for 2-adic. No closed δ* value is known inside; pinning it is
the open prize. Recorded faithfully — no fabricated closure.
