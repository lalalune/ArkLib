# δ* prize core: the subgroup-additive-energy wall, quantified (2026-06-13)

Builds on the clean-moments bridge (swarm commit 674243318: δ* closes iff the
additive energy E_r(μ_n) is near-Gaussian, ≈(2r−1)!!·nʳ, up to r~log(1/ε*)) and
on my proven scaffolding (Bessel main term, cyclotomic-norm excess threshold,
coset symmetry). Here I make the gap to the prize QUANTITATIVE and ground it in
the sum-product literature. **The bridge itself is the swarm's reduction, not
proven here; the results below are conditional on it.** What IS proven here/by
me: the exact-energy main term and the norm threshold.

## The exact (proven) clean threshold is r_max = ½·p^{2/n}

For n=2^μ, e=Σ of 2r roots of unity in ℤ[ζ_n] (degree φ(n)=n/2). The norm
bound |N(e)| ≤ (2r)^{n/2} is exactly AM-GM applied to Σ_j|σ_j(e)|² = rn
(Ramanujan-sum diagonal). A nonzero e in the prime P|p has |N(e)| ≥ p, so
**excess=0 (energy exactly Gaussian baseline) whenever (2r)^{n/2} < p**, i.e.

  **r < r_max := ½·p^{2/n}   [PROVEN, RungBesselEnergy.lean + norm bound].**

This is far stronger than the naive sumset-injectivity threshold n^r<p
(r<log p/log n): for n=16,p=2^128, naive gives r<32 but r_max=3.3×10⁴.

## Three regimes at the prize point (p=2^128, ε*=2^{-128} ⟹ need r~128)

| n (domain)      | r_max=½p^{2/n} | status |
|-----------------|----------------|--------|
| n ≤ 32 (≤2^5)   | ≥ 128          | **CLOSES unconditionally** (clean to r=128 proven) |
| 64,128,256      | 8, 2, 1        | partial: sum-product must cover (r_max,128] |
| n ≥ 512 (≥2^9)  | < 1 (→ 0.5)    | **WALL**: every moment needs sum-product cancellation |

Unconditional-closure boundary: **n ≤ 32** (= 2 ln p / ln 256). The real
FRI/STARK regime (domains 2^20–2^30) sits at r_max=0.5: the proven exact
threshold gives NOTHING; the entire energy is governed by mod-p wraparound,
i.e. by sum-product / Sato–Tate cancellation.

## Why the literature does not reach the prize

Best-known subgroup bounds (papers below):
- **BGK** (Bourgain–Glibichuk–Konyagin): |H|≥p^γ ⟹ max_{b≠0}|η_b| ≤ |H|·p^{−ν(γ)},
  ν(γ)→0 and ν(γ)≪γ. Via max^{2(r−1)}·Parseval this gives clean only when
  n<p^{2ν}, i.e. NOT for n=p^γ (since 2ν<γ).
- **Heath-Brown–Konyagin / Shkredov**: E_2(μ_n) ≪ n^{5/2} for n≤p^{2/3}; sharper
  |R∩(R+μ_1)∩…∩(R+μ_k)| ≪_k |R|^{1/2+α_k}, α_k→0. These control LOW-order
  energy (and only near the n~√p transition); the truth for n≪√p is E_2≈n²
  (clean), but the bounds do not certify cleanliness of the r-th energy up to
  r~log p — they degrade in k.

The prize needs: **the 2r-th additive energy of μ_N within a constant factor
per moment of (2r−1)!!Nʳ, up to r~log(1/ε*)=128, for N a fixed power of p
(N≪√p).** This is strictly stronger than every published sum-product/energy
bound (which reach cleanliness only to r~log p/log N + sub-poly, NOT r~log p).
The shortfall is a multiplicative log N in the attainable moment order — exactly
the long-standing barrier (sub-Johnson RS list decoding, ~25y open). The
cyclotomic-norm view shows WHY the truth is better than the crude bound (AM-GM
is tight only when all conjugates are equal; generic spread → smaller norm →
clean further), and that closing the gap = controlling the SPREAD of the
conjugates Σ_j|σ_j(e)|² beyond its mean rn = precisely the equidistribution
(Sato–Tate/Katz) / higher-energy (Shkredov) input.

## The 5 papers (prize-regime sum-product core)

1. **Kowalski**, *Exponential sums over small subgroups, revisited*,
   arXiv:2401.04756 (2024) — clean modern exposition of BGK; the max|η_b| bound.
2. **Shkredov**, *On additive shifts of multiplicative subgroups*,
   arXiv:1712.00410 / 1102.1172 — k-fold intersection |R∩∩(R+μ_i)| ≪_k |R|^{1/2+α_k}.
3. **Schoen–Shkredov**, *Higher moments of convolutions*, arXiv:1110.2986 —
   higher energies E_k(A)=Σ_x(A∘A)(x)^k, the technology for r-th-order energy.
4. **Heath-Brown–Konyagin / Bourgain–Konyagin**, *Estimates for sums/products
   and exponential sums over subgroups* — E_2(μ_n) ≪ n^{5/2}, the base energy bound.
5. **Green**, *Sum-product phenomena in F_p: a brief introduction*,
   arXiv:0904.2075 — survey situating the regime and the open exponents.

## Honest bottom line

- PROVEN (mine, machine-checked where stated): Bessel main term E_r^∞≤(2r−1)!!nʳ;
  exact clean threshold r<½p^{2/n}; coset symmetry; ⟹ **unconditional δ* closure
  for n≤32 at ε*=2^{-128}** (conditional only on the swarm's clean-moments bridge).
- OPEN (= the prize): near-Gaussian 2r-th subgroup energy to r~log(1/ε*) for
  N≫32 (the FRI regime), a named strengthening of HBK/Shkredov beyond current
  technology. Located precisely; not closed; not fabricated.
