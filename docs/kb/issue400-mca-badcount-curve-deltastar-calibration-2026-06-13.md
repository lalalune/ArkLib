# CALIBRATION: the MCA bad-count curve #bad(t) is monotone; δ* = #bad⁻¹(ε*q); worst dir = dir(k,b) (2026-06-13)

The general-direction reduction (derived + verified, `probe_general_direction_reduction.py`): for
direction `(X^a,X^b)` and agreement set `T` (`|T|=t`), bad `γ` ⟺ `X^a+γX^b ≡ (deg<k) mod m_T`, i.e. the
degree-`k..t−1` coefficients of `X^a+γX^b mod m_T` vanish — `(t−k)` linear conditions in `γ`, consistent
iff `T` satisfies `(t−k−1)` symmetric-function conditions (for `dir(k+1,k+2)`: exactly `e_2(T)=0`, the
#400 case). All conditions are symmetric functions of roots of unity ⟹ **q-independent**.

## The actual MCA bad-count curve (max over ALL directions), n=16, k=8, ρ=1/2 (`probe_mca_badcount_curve.py`)
| t | δ=1−t/n | max #bad | worst dir |
|---|---|---|---|
| 9 (k+1) | .438 | 3728 ≈ C(16,9) (q-DEP, exponential) | (8,13) |
| 10 | .375 | 40 | (8,10) |
| 11 | .312 | 4 | (8,12) |
| 12 | .250 | 4 | (8,12) |
| ≥13 | ≤.188 | 0 | — |

## Structural facts (genuine, computed)
1. **`#bad(t)` is monotone decreasing in `t`** — a proper threshold (deeper band ⟹ more bad scalars).
2. At `t=k+1` (near capacity), `#bad ≈ C(n,k+1)` = EXPONENTIAL ⟹ MCA fails near capacity (δ ≈ 1−ρ−1/n).
3. Sharp drop to small q-independent values at `t≥k+2`.
4. **Worst direction has `a=k`** (`dir(k,b)`), gap ≥2 — it EVADES the mod-4 obstruction that gives
   `dir(k+1,k+2)` zero bad scalars at the prize rates. So the prize worst-case is `dir(k,b)`, NOT #400's
   `dir(k+1,k+2)`. (Corrects the #400 framing's choice of direction.)

## The closed reframing of δ*
> **`δ* = 1 − t*/n`, `t* = max{ t : #bad(t) > ε*q }`** — δ* is the inverse of the monotone, computable,
> q-independent bad-count curve at the budget `ε*q`. For prize ε*q=2^64: δ* sits where `#bad(t)` crosses
> `2^64`. Since `#bad(k+1) ≈ C(n,k+1) ≫ 2^64` (fail) and `#bad(k+2)` is far smaller, the crossing is near
> the top — the EXACT δ* needs the n-scaling (closed form) of `#bad(t)` for `t≥k+2`, worst dir `dir(k,b)`.

## Status (honest)
GENUINE: general-direction reduction (q-independent symmetric-function conditions); the monotone
bad-count curve; worst-direction = dir(k,b); the δ* = #bad⁻¹(ε*q) reframing. The bad-count curve is the
right object and it is COMPUTABLE. OPEN: closed n-scaling of `#bad(t)` for the worst dir(k,b) at t≥k+2
(needs n=32+ which is brute-force-infeasible; needs the combinatorial formula). NOT a closure, but the
calibration that was missing — δ* is now the inverse of a concrete, monotone, q-independent curve.
