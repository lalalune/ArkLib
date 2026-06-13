# Propagation REFUTED at shallow bands → the list curve `L(a)` is combinatorial; `δ*` = `L^{-1}(ε*q)` (2026-06-13)

Honest refutation + refinement, executed (`probe`, not asserted). The moment-hierarchy conjecture's
**propagation step** — "more clean additive moments ⟹ smaller worst-case list" — is **false at
shallow bands**: the worst-case list there is `p`-independent. This re-shapes the open core into a
cleaner, `p`-independent combinatorial object plus the (proven) field-size budget.

## 1. The refutation (data)
`n=8, k=4` (ρ=½), worst-case list (over deep-hole + pairwise-power words) at band `a` vs `p` swept
across the moment-cleanness thresholds `n^j`:

| band `a` (δ) | `p=17` (j*=1.4) | `p=521` (3.0) | `p=4129` (4.0) | `p=32801` (5.0) | `p=262153` (6.0) |
|---|---|---|---|---|---|
| `a=5` (0.375) | 7 | 7 | 7 | 7 | 7 |
| `a=6` (0.250) | 1 | 1 | 1 | 1 | 1 |

The list at `a=k+1` is **`7` for every `p`** — *independent* of how many additive moments are clean.
**Prediction "cleanliness shrinks the list" is refuted at the shallow band.** (Deeper bands `a−k≥2`
have list 0 at `n=8`, so the moment effect there is *inconclusive*, not confirmed — recorded as
untested, not as support.)

## 2. The refinement this forces (the cleaner open form)
The worst-case list curve `L(a)` (max over words of `#{codewords agreeing on ≥a points}`) at shallow
bands is a **combinatorial, field-independent** quantity. Combined with the proven field-size lever
(`censusDomination_pin_largeField`) and the window probe (`L` explodes past `n²` at the capacity
edge `a=k+1` for larger `n`: `273` at `n=16,k=4`; `715` at `n=16,k=8`), the picture is:

> **`δ*` = `1 − a*/n` where `a*` is the band at which the (field-independent) worst-case list curve
> `L(a)` crosses the budget `ε*·q`.** The field size enters **only through the budget** `ε*q`, not
> through `L(a)`. So pinning `δ*` = pinning the *combinatorial* curve `L(a)` for smooth RS, then
> inverting at `ε*q`.

This is *consistent with* and *sharper than* the field-size lever: it says the entire `q`-dependence
of `δ*` is the budget axis, and the hard content is the single `p`-independent curve `L(a)`.

## 3. Why this is genuinely better than the moment-exponent framing
- `L(a)` is **finite, combinatorial, computable per `(n,k,a)`** — no asymptotic exponent, no
  `p`-dependence, no 25-year sum-product constant.
- It plugs directly into the in-tree census: `CensusDomination`'s `K` *is* (an upper bound on)
  `L(a)` summed over scalars; the budget hypothesis `K ≤ ε*q` is exactly `L(a) ≤ ε*q`.
- The **MDS weight distribution of RS is explicit** (Singleton-tight enumerator
  `A_w = C(n,w)(q−1)Σ_j (−1)^j C(w−1,j) q^{w−d_min−j}`), so the *average* list is closed; the open
  gap is purely **worst-case vs average** for the smooth domain — a concentration question on a
  field-independent combinatorial curve, not an additive-energy exponent.

## 4. Updated conjecture ledger (honest)
| candidate | nov | ins | prox | feas | status |
|---|---|---|---|---|---|
| moment-hierarchy δ* (cleanliness ⟹ list) | 9 | 9 | 9 | — | **REFUTED at shallow bands** (list p-independent); retain only the verified *energy facts*, drop the propagation |
| **combinatorial-list-curve δ*** (`δ*=L^{-1}(ε*q)`, `L(a)` field-independent) | 8 | 9 | 9 | 6 | **new, survives the refutation**; open step = pin worst-case `L(a)` (worst-vs-average concentration on smooth RS) |

**Honest status:** the moment-hierarchy *propagation* is dead (refuted); its *energy facts* (quadratic
clean in the prize regime; `E_j` clean ⟺ `p>n^j`) stand and remain a correction to the
energy-exponent framing. The surviving, sharper open object is the **field-independent worst-case
list curve `L(a)` for smooth RS**, with `δ* = L^{-1}(ε*q)`. Feasibility is still `6` (worst-vs-average
concentration unproven), but the object is now combinatorial and `q`-decoupled — the cleanest form yet.

## 5. Next step
Pin `L(a)` at the shallow bands in closed form (the data `7, 273, 715` suggests a binomial — e.g.
`715 = C(13,4)`; test `L(k+1)` against MDS-enumerator-derived formulas), and test worst-vs-average
concentration: is the worst-case `L(a)` within a constant/`poly` factor of the (closed) average for
smooth RS? If yes, `δ*` closes via the explicit MDS enumerator + the field-size budget.

## 6. Closed-form test for `L(k+1)` — INCONCLUSIVE (honest)
Worst-case over deep-hole + pairwise-power candidate words (clean `p`):
`n=8`: `k=2→7, k=3→10, k=4→7, k=5→4`; `n=16`: `k=4→273, k=6→715, k=8→715`.
No clean single binomial fits (`715=C(13,4)` but `273` and the `n=8` row do not align; the sequence
is non-monotonic in `k`). These are **lower bounds** (candidate-limited, not the true max over all
words), so a closed `L(a)` is **not** established here. The combinatorial-list-curve form survives
as the cleanest open object, but `L(a)` does **not** admit an obvious closed form at this resolution
— pinning it remains the open worst-vs-average concentration problem. **No closure claimed.**
