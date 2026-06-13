# The prize is a CUMULANT, not a moment — why the Bessel/moment route stops (#389)

**Status:** genuine new structural understanding from a frontal stab at the char-p excess. Refutes the
"Bessel extends" hope, sharpens the open core to a second-order cumulant. NOT a closure. 2026-06-13.

## The stab and its three sub-refutations

Goal: bound the char-p excess `E_r − E_r^{(0)}` (= spurious balanced 2r-tuples = points of 𝔭∩box of
signed-2r-root-sums) for r up to ln q, n=2^30.

- **(A) geometry of numbers** says expected `#(𝔭∩box) ≈ vol(box)/covol(𝔭) ≈ 2^{−2^28·10.4} ≪ 1` (no
  spurious). **REFUTED:** spurious z are the THIN arithmetic set T_{2r} (signed root-of-unity sums,
  ≤(2n)^{2r} of them), NOT equidistributed in the box; the honest count is |T_{2r}|/p ≈ (2n)^{2r}/p > 1
  for r > log p/(2 log 2n) ≈ 4. Box-volume heuristic fails (T_r arithmetic, not geometric).
- **(B) minimal relation length** L (shortest mod-p vanishing sum of n-th roots): clean for r<L/2. By
  counting, L ≈ log_n p ≈ 8. **REFUTED:** L ≈ 8 ≪ 2 ln q ≈ 354, so clean range misses the needed r≈ln q.

## The new understanding (the genuine content)

For r > log_n p the char-p energy is DOMINATED by equidistribution, not the Gaussian baseline:
  pE_r = n^{2r} (b=0 term) + Σ_{b≠0}‖η_b‖^{2r},   E_r^{(char p)} ≈ n^{2r}/p (1+o(1)).
At r≈ln q≈177, n=2^30: equidistribution term n^{2r}/p ≈ 2^{10718} DWARFS the Bessel baseline
(2r−1)‼n^r ≈ 2^{6549}. So:

1. **The Bessel baseline E_r^{(0)} is SUBLEADING for prize-scale r** — and the moment bound
   E_r ≤ (2r−1)‼n^r is FALSE in char p past r≈8 (by factor 2^{4000+}). The Bessel/moment route to
   B ≤ √(2n ln q) therefore CANNOT reach r≈ln q — it dies at r=log_n p. (This is the precise death of
   the route, not a vague "wall".)
2. **δ* is a CUMULANT, not a moment.** The leading term n^{2r} is exactly the b=0 term and CANCELS in
   `Σ_{b≠0}‖η_b‖^{2r} = pE_r − n^{2r}`. So B = max_{b≠0}‖η_b‖ ≤ √(2n ln q) is governed entirely by the
   SECOND-ORDER fluctuation pE_r − n^{2r} = the cumulant of the period distribution, NOT its raw moment.
   The prize is the connected/cumulant part; the disconnected (equidistribution) part cancels.

## Verdict (honest)
The cumulant framing is genuinely new and explains WHY every moment/energy route (Bessel, GaussianEnergy,
the in-tree GaussPeriodMomentBound) stops at r=log_n p: they bound the RAW moment E_r, but the prize is
the cumulant pE_r − n^{2r}, whose leading raw part cancels. Bounding the cumulant = second-order
equidistribution of the Gauss-sum family uniformly = the irreducible open core (Paley Graph / BCHKS 1.12
/ 0-dimensional arithmetic cancellation). NO new bound emerges — the stab refutes itself into a deeper,
sharper statement of the same open problem. It does NOT pin δ*; it explains precisely why the moment
toolkit cannot, and relocates the target from "moment" to "cumulant." Honest grind: same core, one level
deeper. Not a closure.
