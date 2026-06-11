#!/usr/bin/env python3
"""Probe: refute BoundaryCardStrictInteriorFalseAsStated at a NON-LATTICE Johnson endpoint.

Issue #304 / #232 boundary assembly ground truth.  The in-tree refutations
(BoundaryCardResidualRefutation, ...AffineLineRefutation) kill the bare
closed-boundary residual only at SQUARE endpoints (deg*n a perfect square,
ZMod 5, deg=1).  The non-lattice branch of the quantization split
(boundaryCardResidual_of_not_lattice) defers to the strict-interior supply
`BoundaryCardStrictInteriorFalseAsStated`:

  forall u, forall delta' < delta with floor(delta'*n) = floor(delta*n),
    good set at delta' nonempty  ==>  jointAgreement at delta'.

Claim probed here: that supply is FALSE in general.  Witness:
  F = GF(5), domain = {0,1,2,3} (n=4), deg = 2 (codewords = evals of
  polynomials of degree < 2, i.e. linear), k = 1 (two-word stack),
  u0 = 0, u1 = x^2 on the domain,
  delta = 1 - sqrt(2/4)  (non-lattice: deg*n = 8 not a perfect square),
  delta' = 1/4 < delta,  floor(delta'*4) = floor(delta*4) = 1.

Expected: good set at delta' nonempty (z=0), jointAgreement at delta' FALSE
(needs |S| >= 3, but no linear polynomial agrees with x^2 on 3 of the 4 points).

Consistency check for the CORRECTED (threshold) statement: at delta'=1/4 the
in-tree errorBound is n/q = 4/5 (unique-decoding branch, since (1-rho)/2 = 1/4),
so the k*eps = 1*(4/5) probability threshold demands Pr > 4/5, i.e. card > 4;
witness card must be <= 4 for the corrected statement to survive this witness.
"""

import itertools
import math

q = 5
n = 4
deg = 2          # polynomials of degree < 2
k = 1            # stack of k+1 = 2 words
domain = [0, 1, 2, 3]

# codewords: evals of c0 + c1*x
codewords = []
for c0 in range(q):
    for c1 in range(q):
        codewords.append(tuple((c0 + c1 * x) % q for x in domain))

u0 = (0, 0, 0, 0)
u1 = tuple((x * x) % q for x in domain)
stack = [u0, u1]


def hamming(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def dist_from_code(w):
    return min(hamming(w, c) for c in codewords)


# --- radii ---
delta = 1 - math.sqrt(deg / n)
assert int(math.isqrt(deg * n)) ** 2 != deg * n, "deg*n must NOT be a square"
floor_delta = math.floor(delta * n)
delta_p = 0.25
floor_delta_p = math.floor(delta_p * n)
print(f"delta = 1-sqrt({deg}/{n}) = {delta:.6f}, delta*n = {delta*n:.6f}, "
      f"floor = {floor_delta}")
print(f"delta' = {delta_p}, floor(delta'*n) = {floor_delta_p}")
assert delta_p < delta, "delta' < delta FAILS"
assert floor_delta == floor_delta_p == 1, "floors differ"

# --- good set at delta' (distance <= floor(delta'*n) = 1) ---
good = []
for z in range(q):
    w = tuple((u0[i] + z * u1[i]) % q for i in range(n))
    d = dist_from_code(w)
    if d <= floor_delta_p:
        good.append((z, d))
print(f"good set at delta' (dist <= {floor_delta_p}): {good}")
assert len(good) >= 1, "good set empty — witness broken"

# --- jointAgreement at delta' : need S, |S| >= n - floor = 3, and per-word
#     codewords agreeing on S.  u0=0 is a codeword; binding word is u1. ---
need = n - floor_delta_p
agree_sets = []
for r in range(need, n + 1):
    for S in itertools.combinations(range(n), r):
        for c in codewords:
            if all(c[i] == u1[i] for i in S):
                agree_sets.append((S, c))
print(f"need |S| >= {need}; linear codewords agreeing with x^2 on such S: "
      f"{agree_sets}")
assert not agree_sets, "jointAgreement HOLDS — claim refuted, residual survives"

# same-floor transport: jointAgreement at delta is the same statement
print("jointAgreement at delta' = FALSE  ==> (same floor) FALSE at delta too")

# --- corrected-threshold consistency: errorBound at delta' ---
rho = deg / n
udr_edge = (1 - rho) / 2
assert delta_p <= udr_edge + 1e-12
eps = n / q  # unique-decoding branch of in-tree errorBound
pr_good = len(good) / q
print(f"errorBound(delta') = n/q = {eps}; k*eps = {k*eps}; "
      f"Pr[good] = {pr_good}")
assert pr_good <= k * eps, \
    "Pr > k*eps with no jointAgreement — would refute the STRICT keystone!"
print("corrected threshold statement SURVIVES the witness "
      f"(Pr {pr_good} <= k*eps {k*eps})")

print("\nPROBE VERDICT: BoundaryCardStrictInteriorFalseAsStated is FALSE at the "
      "non-lattice endpoint (k=1, deg=2, n=4, GF(5)); "
      "bare BoundaryCardResidual is FALSE there too (same-floor transport); "
      "threshold-corrected statement consistent.")
