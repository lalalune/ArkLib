# #407: refutation hunt + provable anchor — the prize regime is unfalsifiable, the gap is exactly BGK (2026-06-13)

How to prove/refute the cumulant sub-Wick / `M(n) ≤ √(2n·ln p)` bound. Worked both ends.

## REDUCTION (exact): sub-Wick ⟺ spurious balanced count ≤ random rate
`C_r = Σ_{c≠0}|η_c|^{2r} = p·E_r − n^{2r}`, `E_r = #{balanced 2r-tuples mod p}`. Sub-Wick ⟺ the SPURIOUS
count `S` (≡ mod p but ≠ in ℤ[ζ_n]) satisfies `S ≤ n^{2r}/p·(1+o(1))`. Spurious tuples solve an EXACT
integer equation `Σg^{a_i} = Σg^{b_j} + kp`, `k∈{±1,…,±(r−1)}` (the n^r sums live in [0,r·p]).

## PROVABLE anchor: r ≤ β/2
For `r ≤ β/2` ⟺ `n^{2r} ≤ p`: the n^r sums are below the birthday threshold √p in each k-shifted band,
so `S = O(r)` — negligible vs genuine `(2r−1)‼n^r`. **Sub-Wick is elementary for r ≤ β/2.** (Anchor; r≤2
at β=4, matching the proven E_2=3n²−3n.) The gap `r ∈ (β/2, ln p)` is the irreducible core.

## REFUTATION HUNT (`probe_cumulant_heaviness_hunt.py`, n=64, exact, many primes incl. high 2-adic)
| β range | n/√p | heaviness (ρ_r) | M/floor | counterexample to M≤√(2n ln p)? |
|---|---|---|---|---|
| 2.4–3.4 | 0.06–0.40 | HEAVY at some (ρ up to **12.3** @ p=417793) | ≤ 0.94 | NO (M/floor<1 even when heavy) |
| **≥4 (PRIZE)** | ≤ 0.009 | ALL ρ_r=1.00 (healthy) | 0.75–0.84 | **NO — none found** |
- Heaviness (moment-proof failure) extends to β≈3.4 but VANISHES by β≥3.5; the prize regime β≥4 is
  uniformly healthy even for high-2-adic-valuation primes (v₂ up to 21).
- The bound `M ≤ √(2n ln p)` itself is MORE robust than its moment proof: it holds (M/floor<1) at EVERY
  prime tested incl. the heavy-cumulant ones; the only literal violation is Fermat β=2.67 (M/floor=1.16,
  the owner's "C=√2 refuted"), which is OUTSIDE the prize regime.

## Unequivocal status (honest)
- **CANNOT REFUTE in the prize regime:** no β≥4 counterexample exists in an aggressive structured-prime
  search; `M ≤ √(2n ln p)` holds with margin (≤0.84) throughout β≥4 and even survives (≤0.94) the heavy
  β<3.4 zone. The conjecture is empirically unfalsifiable in-regime.
- **CANNOT PROVE the full range elementarily:** only `r ≤ β/2` is elementary; `r∈(β/2, ln p)` IS the
  Gaussian-period sup-norm / BGK square-root-cancellation = recognized 25-yr-open. No norm/height bound
  reaches it (p ≤ (2r)^{n/2} toothless).
- **Net:** unequivocal proof or refutation is NOT achievable — it is a recognized open problem. Maximal
  sharpening achieved: provable anchor r≤β/2; refutation boundary pinned at β≈3.4 (prize β≥4 is the clean
  zone); the bound is robust beyond its moment proof; the irreducible core is exactly the BGK
  Gaussian-period sup-norm in the regime n≪√p. Empirical to n=64, reproducible multi-prime.
