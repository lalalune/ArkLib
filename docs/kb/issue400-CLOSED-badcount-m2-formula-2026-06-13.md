# CLOSED FORMULA for the m=2 bad-count: Σ_s C(N/2,s)2^s — purely binomial, NO additive energy (2026-06-13)

The crux test (is `#bad(t)` closed-combinatorial or does it re-encode additive energy?) — answered for the
`m=2` band: **CLOSED, purely binomial.**

## Derivation (Lam–Leung single-pattern)
For 2-power roots, the ONLY linear relations among `ζ^i` are antipodal (`ζ^i+ζ^{i+N/2}=0`). So
`Σ_{i∈I}ζ^i` is determined entirely by the **single-pattern**: which antipodal pairs contribute exactly
one element (with sign ±); full/empty pairs contribute 0. Two j-subsets collide iff same single-pattern.
Counting patterns with `s` "single" pairs (`s≡j mod 2`, `s≤min(j,N−j)`):
> **`#{distinct subset-sums of j-subsets of μ_N} = Σ_{s≡j (2),  0≤s≤min(j,N−j)} C(N/2, s)·2^s`.**
VERIFIED exactly vs brute force (`probe_closed_badcount_m2.py`): N=8 j=2→25 (=1+6·4); N=16 j=4→1233
(=1+112+1120); all N≤16, all j match.

## Connection to the MCA bad-count
The `m=2` band (worst dir = `dir(k,k+2)`) has condition `\hat{1_A}(1)=0` ⟺ A = antipodal-pair union ⟹
readout `\hat(2) = 2·(subset-sum of w/2 elts of μ_{n/2})`. So
> **`#bad(m=2, w) = Σ_{s≡(w/2)(2), s≤min(w/2, n/2−w/2)} C(n/4, s)·2^s`**  — closed, q-independent, binomial.
Dominant term `C(n/4, w/2)·2^{w/2}` ⟹ exponential ⟹ MCA fails at this near-capacity band (as expected).

## Why this matters (the crux, positively resolved for m=2)
- The count is **purely binomial — NO subgroup additive energy, NO character sum.** So at least the m=2
  level of δ* is genuinely closed combinatorics, OFF the hard analytic wall. Strong positive sign that the
  whole δ* characterization is closed.
- The formula is `Σ_s C(n/4,s)2^s` = sum over the **single-rank s** (the signed-single decomposition). The
  Kambiré construction = a single-s term ⟹ it is a LOWER bound, NOT extremal; generic flat sets give the
  full sum. So the true δ* uses the full closed sum, ≤ the construction's bracket.

## Next (the recursion)
Higher m: `\hat(2)=0` is itself a vanishing sum of (n/2)-th roots ⟹ antipodal again ⟹ the count recurses
down the 2-adic tower, giving a NESTED closed binomial formula for `#bad(m)` at each level. If this closes
(being verified at m=4), then `δ* = 1 − t*/n` with `t*` from inverting a closed nested-binomial count =
a fully CLOSED, q-independent δ*. The m=2 closed formula is the base case, verified.

## Status
GENUINE/verified: closed binomial formula for #bad(m=2), purely combinatorial (no additive energy).
This positively resolves the crux at the base level. OPEN: the nested recursion for general m (in
progress at m=4); the worst-direction-over-b map for odd m. RETRACTED earlier: s_max=μ−1. Strongest
evidence yet that δ* is closed-combinatorial, not the recognized-hard problem.
