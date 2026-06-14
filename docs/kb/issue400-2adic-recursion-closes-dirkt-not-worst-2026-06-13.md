# 2-adic tower recursion CLOSES the dir(k,t) bad-count — but dir(k,t) is NOT the worst direction (2026-06-13)

## The recursion (VERIFIED, n=16 all cases; analytic via \hat_A(2j')=2\hat_B(j'))
For the Fourier-flat / dir(k,t) bad-count `#bad_n(k,m) = #{distinct \hat_A(m) : |A|=k+m, \hat_A(1..m-1)=0}`:
When `\hat_A(1)=0`, A = antipodal-pair union ↔ B⊆ℤ/(n/2). Then `\hat_A(odd)=0` automatically and
`\hat_A(2j')=2\hat_B(j')`. Hence:
> **`#bad_n(k, 2m') = #bad_{n/2}(k/2, m')`,  and `#bad_n(k, m)=0` for m odd.**
Verified: n=16 vs n=8 match for ALL (k,m); odd-m = 0.

## Consequence: CLOSED nested-binomial formula
`#bad ≠ 0` ⟺ `m = 2^a`. Recursing a−1 times to the base `#bad_N(K,2)` = subset-sums of (K+2)/2-subsets
of μ_{N/2} = the closed binomial `Σ_{s≡· , s≤·} C(N/4,s)2^s`. So
> **`#bad_n(k, 2^a)` is a CLOSED nested-binomial expression** (q-independent, no additive energy), and the
> bad-count is supported only at power-of-2 band depths `δ = 1−ρ−2^a/n`.

## HONEST scope: dir(k,t) is NOT the worst direction
Plugging prize params (ρ=1/2): this formula crosses ε*q at `δ* ≈ 0.484`, but the PROVEN Kambiré
construction upper bracket is `δ* ≤ 0.441`. Since 0.484 > 0.441, the **construction direction
(`dir((r−1)m, rm)`, gap `m=n/s`) produces MORE bad scalars** at those bands than `dir(k,t)` does. So:
- `#bad_dir(k,t)` is a LOWER bound on the true MCA bad-count ⟹ an UPPER bound on δ* (0.484), weaker than
  the construction's 0.441.
- At n=16 `dir(k,t)` matched the all-direction max at the shallow bands (t=10,12), but at the DEEPER
  prize-relevant bands the large-gap construction direction dominates.

## Status (honest)
GENUINE/verified: the 2-adic tower recursion + closed nested-binomial formula for the dir(k,t) family;
bad-count supported only at power-of-2 depths; all q-independent, no additive energy (crux stays clean).
NOT the prize closure: the WORST direction is the large-gap construction one (`dir(a,a+n/s)`); its count
is `C(s,r)` and the remaining question is its EXTREMALITY (cf sibling #407 "optimality count survives").
The right next step: apply the same antipodal/tower machinery to the LARGE-GAP direction to get its
closed count and prove C(s,r) extremal ⟹ closed δ* = 1−ρ−2/s*. RETRACTED earlier: s_max=μ−1.
