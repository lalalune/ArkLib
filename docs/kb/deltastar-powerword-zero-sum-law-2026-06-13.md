# delta* note: the all-k power-word list is a zero-sum fiber

Date: 2026-06-13

Lean anchor: `ArkLib/Data/CodingTheory/ProximityGap/PowerWordListBound.lean`

Issue anchors: #389, #371

## Result

For any finite field, injective domain `dom : Fin n -> F`, and Reed-Solomon
dimension `k`, the received word

```text
w(i) = dom(i)^(k + 1)
```

has an exact sub-Johnson list at agreement `k + 1`:

```text
#{ c in RS(dom,k) : |agree(c,w)| >= k+1 }
  =
#{ T subset domain : |T| = k+1 and sum_{x in T} x = 0 }.
```

The machine-checked theorem is `powerWord_list_eq_sumZero`.  Its core mechanism is
also recorded as `powerWord_explainable_iff_sumZero`: a `(k+1)`-core is explainable
by a degree-`< k` codeword iff its domain values sum to zero.  The additional
`powerWord_agreeSet_card_le` root-count cap is what upgrades the core
characterization into an exact list-size identity, not just a supply lower bound.

## Why it works

For `T = {x_i}` with `|T| = k+1`, set

```text
Q_T(X) = product_i (X - x_i).
```

The forced explainer is `X^(k+1) - Q_T(X)`.  Vieta says the coefficient of `X^k`
in `Q_T` is `-sum_i x_i`; therefore the degree drops below `k` exactly when
`sum_i x_i = 0`.  Conversely, any degree-`< k` explainer makes
`X^(k+1) - P` and `Q_T` monic degree-`k+1` polynomials with the same `k+1`
roots, so they are equal and Vieta forces the zero-sum condition.

## Ten connections to the current campaign

1. **Cubic orchard is the `k = 2` shadow.**  `CubicOrchardIdentity.lean` is not an
   isolated cubic accident.  It is the first visible member of the all-`k`
   power-word law.

2. **The full-field ceiling is tight for every rate.**  On unstructured domains
   close to the full field, the zero-sum fiber has the expected `Theta(n^k)`
   scale, matching the sub-Johnson list ceiling up to the fixed factorial
   constant.  A field-blind sub-Johnson theorem cannot be true.

3. **Smooth suppression is exactly additive-combinatorics suppression.**  On
   `mu_n`, the same list size becomes a zero-sum subset count in a multiplicative
   subgroup.  The coding-theory question has become a higher additive-energy
   question about the evaluation set.

4. **The cubic additive-energy bound generalizes in the right language.**  The
   `k = 2` Cauchy-Schwarz bridge bounds zero-sum triples through additive energy.
   For higher `k`, the analogous objects are higher additive energies and
   subset-sum fiber moments, not new RS-specific geometry.

5. **Exactness removes overcount ambiguity.**  `powerWord_agreeSet_card_le` proves
   that every listed codeword agrees in exactly `k+1` places.  Thus the zero-sum
   core count is the list count, rather than a supply count with possible
   multiplicities hidden in the fibers.

6. **It aligns with `EsymmFiber.lean`.**  The new theorem is the `m = 0`,
   `W = X^(k+1)` exact-list specialization of the forced-polynomial/Vieta view in
   `EsymmFiber.lean`.  The deeper band `t = k+m+1` should ask for the first
   `m+1` elementary symmetric functions of a `t`-set to hit the top-coefficient
   targets forced by `W`.

7. **It explains why dyadic coset-unions are dangerous.**  `EsymmFiber.lean`
   shows that smooth dyadic domains can have many sets with several leading
   elementary symmetric functions vanishing.  The power-word result identifies
   the first rung of that same ladder as the zero-sum rung.

8. **It unifies subset-sum and elementary-symmetric lanes.**  The older
   zero-sum/pairing inflations, `SubsetSumEsymmVanishing`, and the dyadic
   `EsymmFiber` construction are all coefficient-cancellation statements for
   node polynomials.  Future attacks should pass through this Vieta dictionary
   first.

9. **It gives a clean red-team test for proposed #389 bounds.**  Any proposed
   supply or list bound must dominate the zero-sum `(k+1)`-fiber of `dom`.  If a
   conjectured smooth-domain estimate fails this test, it is already dead at
   `m = 0`.

10. **It sharpens the delta* ceiling consumer.**  When a production bad-side
    construction uses a degree-`t` received word, the remaining domain-dependent
    quantity is not mysterious RS list geometry.  At least for the power-word
    edge, it is an explicit symmetric-function fiber count.  Pinning delta*
    should therefore track the asymptotics of these fibers on the deployed
    smooth domains.

## Next formal targets

- Prove the full exact-list analogue of `EsymmFiber.explainable_iff_forcedPoly_degree`:
  for `t = k+m+1` and `W.degree = t`, codewords agreeing with `eval W` on at least
  `t` points are in bijection with `t`-subsets whose first `m+1` elementary
  symmetric values hit the top-coefficient targets.
- Specialize that theorem to `W = X^(k+m+1)`, yielding the clean vanishing window
  `e_1 = ... = e_(m+1) = 0`.
- Feed the resulting exact count into the #389 supply ledger as the canonical
  lower-bound obstruction any `SmoothDomainTwoRegimeLaw` must include.
