# The δ* keystone E_{F_p}(μ_n): exact value vs robust bound (#389)

The δ* floor reduces to the additive energy E_{F_p}(μ_n). Three probes (independent
code, exact integers) settle its structure. Verdict: **target the BOUND, not the value.**

## 1. The exact value & its threshold (probe_energy_keystone_verify + _threshold_exact)
- `E_{F_p}(μ_n) = 3n(n−1)` (the clean char-0 value) **⟺ p divides no quadruple cyclotomic
  norm** `N(ζ^i+ζ^j−ζ^k−ζ^l)`. The bad primes form a finite explicit set (≡1 mod n).
- This is a DIVISIBILITY condition, not a power threshold; the surplus is non-monotone in p.
  So a lemma "E=3n(n−1) for p ≥ n^c" is FALSE as stated.

## 2. P_max(n) grows SUPER-polynomially (probe_energy_pmax_growth)
- Largest bad prime: n=8 → 41 (n^1.79), n=16 → 337 (n^2.10), **n=32 → 21,523,361 (n^4.87)**.
- Bounded only by max|norm| = 4^(φ(n)) = 4^(n/2). So the exact-value threshold is delicate:
  for production n, a specific prime is NOT guaranteed clean by being "large" — the bad set
  can in principle reach ~4^(n/2). The exact-value route needs the explicit coprimality.

## 3. BUT the BOUND E ≤ C·n² is ROBUST at every prime (probe_energy_badprime_bound) — KEY
- At the LARGEST bad prime p=21,523,361 (n=32): surplus only +128, **E/n² = 3.03**.
- At small bad primes (p=4129): surplus +768, E/n² = 3.66. Across ALL tested primes
  (clean and bad, n=8..32): **E/n² ∈ [3.0, 3.7], i.e. E ≤ 4n² holds everywhere.**
- Mechanism: surplus magnitude is governed by the NUMBER of coincident quadruples (small —
  the few relations whose norm hits p), NOT by p's size. Large bad primes ⟹ fewer
  coincidences ⟹ smaller surplus. So P_max growing super-poly does NOT break the bound.

## Implication for the keystone formalization
The δ* floor needs `E_{F_p}(μ_n) ≤ C·n²`, NOT the exact value 3n(n−1). Target the BOUND:
it is robust to the (super-polynomially large) bad-prime set, holding at every prime tested
with C ≈ 4 — no delicate divisibility hypothesis needed. The exact-value statement (with its
super-poly threshold) is the harder, more fragile object and is not what the pin requires.

Honest caveat: all sampled (n ≤ 32, specific primes); HBK worst case is E ≪ n^2.5 > n², so
`E ≤ Cn²` is not proven unconditional — but no blow-up appears even at the extreme bad prime,
so the worst case (if realized) needs a genuinely adversarial subgroup not seen here. The
Stepanov route the fleet is formalizing is exactly the unconditional proof of this bound.
