# The Galois-prime mechanism for the bad-prime bound (#407, 2026-06-14)

## The structured bad-scalar config = multi-Galois-prime divisibility (new, verified)
The char-p "spurious" bad-scalar config is a non-negation-symmetric subset `S ⊆ μ_n` (n=2^μ)
satisfying the window power-sum constraints `e_1 = e_3 = … = e_{2r-1} = 0` over `F_p`. INDEPENDENTLY
REPRODUCED the swarm's exact bad-prime sets with the 2-constraint object `Σ_S x ≡ 0 ∧ Σ_S x³ ≡ 0`:
n=16→{17}, n=32→{97} (vs the 1-constraint object's 9, 30 bad primes — the second constraint is the
suppressor).

**Mechanism (Galois).** `Σ_S x ≡ 0` in `F_p` ⟺ `α = Σ_{i} ζ^{a_i} ≡ 0 mod P` for the prime `P|p`
of the chosen embedding `ζ↦g`. Since `x↦x³` is the Galois automorphism `σ₃` (gcd(3,2^μ)=1),
`Σ_S x³ ≡ 0` ⟺ `σ₃(α) ≡ 0 mod P` ⟺ `α ≡ 0 mod σ₃⁻¹(P)` — a DIFFERENT prime above `p`. Thus the
`r` odd-power constraints `e_1,e_3,…,e_{2r-1}=0` ⟺ `α ≡ 0 mod (P₁·P₃·…·P_{2r-1})`, `r` distinct
Galois-conjugate primes above `p`. Hence

  **`p^r | N(α)`  ⟹  `p ≤ N(α)^{1/r}`.**

VERIFIED: n=16,p=17,config{0,1,2,6,7,13}: `N(α)=334084`, `v₁₇=4≥2`; n=32,p=97,{0,1,2,6,20}:
`N(α)=88529281`, `v₉₇=4≥2`. The bad-prime bound improves by a factor `r` in the exponent — this is
exactly WHY more window constraints suppress harder (each constraint forces one more prime divisor).

## Why it does not (yet) close, honestly
`N(α) ≤ s^{φ(n)} = s^{n/2}` for `α` a sum of `s` roots of unity, so `p ≤ N(α)^{1/r} ≤ s^{n/(2r)}`.
For the prize (`r≈11`, `n=2^24`, `q=n^β`) this is still `≫ q`: the worst-case norm bound is loose
(predicts ≤578 for n=16, actual bad prime 17). Closing requires `N(α) < q^r` for the structured
configs, i.e. the structured `α` have SMALL norm — but over ℂ they are non-neg-symmetric with
`|α|~√s`, so `N(α)` is genuinely large. The gap between the loose `N(α)^{1/r}` and the true small bad
primes (`< N₀ = |H^{(+r)}| ~ ε*q`) is the residual structural cancellation = the BGK/Paley open core.

## Value
Novel lens (the multi-constraint suppression = multi-Galois-prime divisibility, `p^r|N(α)`),
verified, connects the bad-prime bound to the cyclotomic norm (my RungBesselEnergy/norm-threshold
lane). Improves the bound by factor `r`. Does NOT close (the norm is large); the exact `< N₀` bound
is the open core. Genuine contribution + honest limit.

## CORRECTION (2026-06-14, effective-Dvornicich–Zannier probe): N₀(n) is QUASI-polynomial, NOT n^3.5
The attack-wave synthesis claimed `N₀(n) ~ n^{3.4–3.7}` (polynomial) so the prize prime
`q≈n·2^128 ≫ N₀` would be faithful. **This is a SCAN-TRUNCATION ARTIFACT and is wrong.** Direct
attack on the effective DZ threshold (the deployed object `γ_T = −DD_T(x^a)/DD_T(x^b)`, bad scalars
= ratios of Schur/divided-difference values in `Frac(ℤ[ζ_n])`):

- **The bad primes are exactly factors of `Norm_{ℚ(ζ_n)/ℚ}(γ_{T₁}−γ_{T₂})`** (EXACT-verified: at
  n=16 the largest bad prime `ℓ=102769` divides `N(γ_{T₁}−γ_{T₂})=205538=2·102769` for the merging
  pair `T₁=(3,4,6,9),T₂=(0,5,9,11)`). So `N₀` is the largest such norm factor `≡1 mod n`, `>n²`.
- **Conway–Jones (Acta Arith. 1976, Thm 3.2): `Σ_{p|Q}(p−2) ≤ k−2`** bounds the ORDER's prime
  divisors by the term-count k — but the **DZ02 mod-ℓ version leaves the modulus ℓ UNBOUNDED**
  (ℓ enters as an extra allowed prime divisor; only the *other* divisors are k-bounded). So DZ/CJ
  give NO bound on the bad prime ℓ in terms of the term-count. The threshold is governed by the
  HEIGHT of `γ_{T₁}−γ_{T₂}` in `ℚ(ζ_n)` (degree `φ(n)=n/2`), not by w.
- **MEASURED (exact symbolic resultant norms, w=3, dir(3,5), ground-truth LBs on N₀):**
  | n | μ | N₀ ≥ | log_n | log₂ |
  |---|---|---|---|---|
  | 16 | 4 | 104 849 | **4.17** | 16.7 |
  | 32 | 5 | 8.36×10⁹ | **6.59** | 33.0 |
  | 64 | 6 | 1.53×10¹⁷ | **9.51** | 57.0 |
  The log_n exponent **RISES** (4.17→6.59→9.51, increments ~2.5/μ-step) ⟹ `N₀ ~ n^{Θ(μ)} =
  n^{Θ(log n)}`, **quasi-polynomial** (`log₂N₀ ~ 2.7μ²`). The n=16 LB (104849) matches the full
  `𝔽_q` scan's true N₀ (102769–104849), so the symbolic LBs are tight.
- **`N₀` is band-INDEPENDENT** (w=3 and w=4 both give N₀≈10⁵ at n=16) — confirms it is field-,
  not term-, controlled. The earlier "n^3.5" came from `𝔽_q` scans truncated at a ceiling
  `< n^{4.5}` (the same small-q truncation trap the issue warned about, here biting N₀ itself).
- **PRIZE VERDICT.** Faithful needs `log₂N₀ < μ+128`. Even FREEZING the exponent at its n=64 value
  (`N₀=n^{9.51}`), `log₂N₀=9.51μ` exceeds `μ+128` for all **μ≥14**; the quadratic fit gives
  `log₂N₀ ≈ 1200` (μ=20) … `6400` (μ=43) ≫ budget 148…171. **Effective DZ does NOT close the
  equality/threshold gap** — the growing field degree `φ(n)=n/2`, not the term-count, defeats the
  polynomial bound. The bad-prime set is FINITE (factors of a fixed norm) but its largest element is
  quasi-poly in n and lands ABOVE the prize prime.
- **What survives:** the deviation is ALWAYS negative (count drops, never exceeds char-0) at every
  tested prime — the **ring-hom merge-only monotonicity `N(char-p) ≤ N(char-0)` (no-excess half)
  holds**. Only the EQUALITY (exact faithfulness) fails: at the prize prime, char-p can MERGE bad
  scalars the char-0 count keeps distinct, so the deployed count can be `< budget` there. Whether a
  merge-induced drop is harmful (under-counts a band) or harmless (still saturates the cap) is the
  remaining open question — but the "N₀ polynomial ⟹ prize faithful" route is REFUTED.
  Probes: `/tmp/dz_threshold.py`, `dz_exponent.py`, `dz_mechanism.py`, `dz_w_scan.py`, `extrap.py`.
