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
