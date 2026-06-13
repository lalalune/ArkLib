# A non-moment route via the Favard-length / self-similar method (#389)

**Status:** novel cross-field lead from the arXiv sweep — the FIRST non-moment candidate that matches
the dyadic structure. Honestly scored; a research lead, not a closure. Author: δ* lane, 2026-06-13.

## Why this shelf (the impossibility map demanded a non-moment method)

The session's impossibility map proved every moment method stalls at `k<log_n p` and every energy
method is √-lossy. The ONLY escape is a non-moment bound on `B(μ_n)=max_b|η_b|`. Subgroup-Burgess
(BGK/Kerr–Shparlinski/di Benedetto) needs `n>p^{1/4}` and reaches only `n^{1−δ}` — useless at the prize
`n≈p^{1/8}`. The recent crypto MCA notes (Haböck 2025/2110, 2025/2051) prove MCA only UP TO Johnson
(Guruswami–Sudan, "same bound as ordinary CA [BCIKS20 Thm 5.1]") — not above. So the lever, if any,
is in a DIFFERENT field.

## The lead: Favard length of self-similar sets via vanishing sums of roots of unity

A harmonic-analysis / geometric-measure-theory program — **Nazarov–Peres–Volberg** (4-corner Cantor
set, Favard length `≤ n^{−c}`), **Bond–Łaba–Volberg**, **Łaba–Marshall** (arXiv 2202.07555, Discrete
Anal. 2022) — controls the **sup/L¹-norm decay of products of trigonometric polynomials whose
frequencies are roots of unity**, `∏_k φ(N^k t)`, using as its engine the **classification of vanishing
sums of `N`-th roots of unity** (Lam–Leung / Poonen–Rubinstein, improved by Łaba–Marshall). Crucially:

1. **It is NON-MOMENT.** It bounds the sup/L¹ norm via the *combinatorial structure of where the
   polynomial's zeros (= vanishing sums) sit*, NOT via even moments — so it is not subject to the
   `k<log_n p` diagonal wall.
2. **It is built for SELF-SIMILAR / iterated structure** `∏_k φ(N^k t)` — and the deployed dyadic
   subgroup `μ_{2^k}` IS a self-similar tower: squaring `x↦x²` maps `μ_{2^j}` 2-to-1 onto `μ_{2^{j−1}}`,
   so `μ_{2^k}` is the `k`-fold iterate of the doubling map. The Gauss-period `η_b` is the Fourier
   coefficient of this iterated set — exactly the object the Favard method estimates.
3. **The finite-field analogue exists**: vanishing sums of `m`-th roots of unity in char `p`
   (arXiv math/9605216) govern the char-`p` coincidences = the halo excess in our cyclotomic-lattice
   reformulation. The Favard machinery's number-theoretic core transfers to exactly this object.

## The conjecture / route

> **(Favard-route.)** The dyadic Gauss-period sup-norm `B(μ_{2^k}) = max_b|η_b|` obeys the same
> power-saving the Favard-length method gives for the `k`-fold doubling self-similar set, namely
> `B ≤ √p · (2^k)^{−c} · polylog`-type decay driven by the Łaba–Marshall vanishing-sum lower bound —
> and tracking the constant through the char-`p` vanishing-sum classification (math/9605216) yields the
> Salem–Zygmund value `√(n log p)`. The non-moment vanishing-sum engine replaces the (walled) moment
> method; the self-similar tower supplies the iterated structure the method requires.

## Refutation / honesty caveats (this is a LEAD, not a transfer)

- **The transfer is unestablished.** Favard sets live in `ℝ/ℤ` with base-`N` digit self-similarity;
  `μ_{2^k}` is a multiplicative subgroup in `F_p`. The doubling-map self-similarity is a real structural
  match, but the Fourier dictionary (`ℝ/ℤ` arcs ↔ `F_p` additive characters) must be built — it is NOT
  a drop-in. This is the genuine open work; the lead could fail to transfer.
- **Decay rate vs target.** NPV gives `n^{−c}` with small `c` (like BGK's `δ`); reaching the sharp
  `√(n log p)` needs the *sharpest* Łaba–Marshall vanishing-sum input AND the char-`p` refinement —
  whether these compose to `1/2` (not just `δ`) is open, exactly the prize's quantitative crux.
- **Consistent with all in-tree facts**: non-moment (escapes the proven wall), uses the dyadic tower
  (which generic-`μ_n` measurements showed is the special case), and bottoms out on char-`p` vanishing
  sums (the in-tree halo object). No contradiction with the 5 axiom-clean bricks or §R.3.

## Honest scores
novelty 9 (a GMT/harmonic-analysis method on the prize, never attempted in the campaign) /
insight 9 (self-similar tower ↔ Favard iterated product ↔ vanishing sums, a real triple match) /
proximity 8 (dyadic prize domain; the `n≈p^{1/8}` quantitative transfer is the caveat) /
feasibility 4 (non-moment so NOT wall-blocked, but the `ℝ/ℤ→F_p` transfer + sharp-constant are
unestablished research). **The best new lead of the sweep — the only non-moment route that fits the
dyadic structure. Not a closure; the transfer is the open work.**

## Papers to pull (the lead's lineage)
- Łaba–Marshall, **Vanishing sums of roots of unity & Favard length of self-similar product sets**,
  arXiv **2202.07555** (Discrete Anal. 2022) — the freshest, improves Lam–Leung, the entry point.
- Bond–Łaba–Volberg, **Favard length and quantitative rectifiability / number-theoretic Favard**
  (and Nazarov–Peres–Volberg, *Ann. Math.* 2010, 4-corner Cantor `n^{−c}`) — the method.
- **On vanishing sums of `m`-th roots of unity in finite fields**, arXiv **math/9605216** — the
  char-`p` engine = the halo coincidences.
- Poonen–Rubinstein / **Classifying minimal vanishing sums of roots of unity**, arXiv 2008.11268 —
  the vanishing-sum classification the bound consumes.
