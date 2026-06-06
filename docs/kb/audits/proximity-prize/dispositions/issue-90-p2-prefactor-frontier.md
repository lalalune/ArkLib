# Issue #90: P2 Prefactor / Restricted Match Frontier

**Status:** clarified 2026-06-06. No proof terms changed.

The original issue wording was based on older wave notes that described
`HenselNumerator.prefactor` as carrying an explicit X-Taylor binomial. That is no longer the
current source state.

## Current Source Facts

- `prefactor i i1 lam = lam.parts.countPerms`, proved by
  `BCIKS20.HenselNumerator.prefactor_eq_countPerms`.
- `PrefactorWeightMatch` is already proven by `prefactorWeightMatch_holds`; it is exactly the
  zero-peeling identity
  `countPerms (replicate j0 0 + lam) = C(j0 + card lam, card lam) * countPerms lam`.
- `hasseDerivY_coeff` supplies the missing Y-Hasse binomial
  `C(i + m, m)` from coefficient extraction. The binomial is not stored in `prefactor`.
- `P2_closed_of_restrictedMatch` already proves that `RestrictedFaaDiBrunoMatch` closes the P2
  root/lift package.

## What Remains

The remaining obligation is the term-level proof of `RestrictedFaaDiBrunoMatch`, not a standalone
definition edit to `prefactor`.

Reasonable proof sub-bricks:

1. Reindex the restricted value-multiset sum in `restrictedFaaDiBrunoSum` to the `(A.1)` recursion
   indices `(i1, λ)`, preserving the `(t + 1) ∉ m` / `(t + 1) ∉ λ.parts` guard.
2. Connect the lifted `Q` coefficient term through `coeff_Q_eq_B` to the representative inside
   `B_coeff`, including the `hasseDerivY_coeff` coefficient shift.
3. Transport the positive-part `prefactor_eq_countPerms` and the proven zero-peel identity through
   the reindexing.
4. Assemble `partitionProd_coeff_assembled`, `exponent_balance_ξ`, `exponent_balance_W`, and the
   `ζ` sign/denominator-clearing convention into the equality of values.
5. Package the term equality as a `Finset.sum_congr` proof of `RestrictedFaaDiBrunoMatch`; the
   existing `P2_closed_of_restrictedMatch` then closes the P2 endpoint.

## Cleaned-Up Stale Notes

Updated comments and audit notes that still described the obsolete
`C(R.natDegree, i1) * multinomial` prefactor:

- `P2Vanish.lean`
- `P2Close.lean`
- `HenselNumerator.lean`
- `pc-w11-bridge.md`
- `pc-w14-last.md`
- `pc-w16.md`
- `pc-w3-build.md`
- `pc-w3-faadibruno-scout.md`
- `pc-w4b-bridge.md`
