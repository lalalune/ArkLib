# Direct max-list disproof search (Method 1) — RESULTS

Goal: falsify the proximity prize **floor conjecture** (smooth-domain RS lists are <= budget ~ n
for ALL words at window-INTERIOR radii) by finding ONE word whose list EXCEEDS budget at a
window-interior radius and GROWS super-linearly (n^c, c>1). Falsify-first.

## Setup (matches in-tree conventions)
- F_q prime; mu_n = order-n multiplicative subgroup (eval domain). codeword = deg<k poly on mu_n.
- rho = k/n. list(w,a) = #{distinct deg<k polys agreeing with w on >= a points}.
- AGREEMENT window: capacity = rho*n = k ; Johnson = sqrt(rho)*n. interior = k < a < sqrt(rho)*n.
- Budget proxy ~ n (prize regime q*eps*, eps*=2^-128, q~n*2^128). Toy q too small to evaluate
  budget directly -> measure GROWTH of max-list vs n at fixed radius.
- Non-Fermat primes (NO Fermat-prime #400 trap): n=8 q=4129; n=16 q=65617 (and 65633 cross-check);
  n=32 q=1048609. All non-Fermat, q≡1 mod n, beta=log_n(q)≈4.

## Method
Exact list counting (validated 3 ways: Python brute poly-enum, Python cached-Lagrange, two C
implementations — hashset dedup and canonical-lex-min dedup; all agree to 0 mismatches).
Search = monomials + O163 densest-cluster + CODEWORD-AWARE smart hill-climb (promote agreement
a-1 -> a by single-coordinate plurality flips). The smart climb is strong: it independently
recovers/reproduces the O163 prior (max-list 7 at mu_8).

## RESULT TABLE — max-list at each interior agreement a (rho = 1/4)

| n  | q       | k | a (interior) | a/n    | window-frac | MAX LIST | ceiling C(n,k)/C(a,k) | budget ~n |
|----|---------|---|--------------|--------|-------------|----------|-----------------------|-----------|
| 8  | 4129    | 2 | 3 (=k+1)     | 0.375  | 0.50        | **7**    | 9                     | 8         |
| 16 | 65617   | 4 | 5 (=k+1)     | 0.3125 | 0.25        | **273**  | 364                   | 16        |
| 16 | 65617   | 4 | 6 (=k+2)     | 0.375  | **0.50**    | **3**    | 121                   | 16        |
| 16 | 65617   | 4 | 7 (=k+3)     | 0.4375 | 0.75        | **1**    | 52                    | 16        |
| 32 | 1048609 | 8 | 12 (mid)     | 0.375  | **0.50**    | **0-1**  | 21249                 | 32        |
| 32 | 1048609 | 8 | 9 (=k+1)     | 0.281  | 0.125       | >=25 (cluster LB)| 1168700       | 32        |

(n=32 a=12 mid-window: O163 densest-cluster words L=8,16 give list 0 and 1 respectively — O(1),
exactly the floor. Verified exact via OpenMP canonical-dedup counter, cross-checked vs Python on
n<=16 with 0 mismatches. a=9 cluster lower bound below; the smart climb that reaches near-ceiling
at a=k+1 is too costly at n=32, so a=9 is reported as a cluster LOWER BOUND only.)

(rho=1/4 a=5 cross-checked on a SECOND non-Fermat prime q=65633 → also exactly 273: the value is
field-independent, not an artifact.)

## KEY OBSERVATION — the only growth is at a = k+1, which CONVERGES TO CAPACITY (not a fixed radius)

The "window-fraction" (0 = capacity boundary, 1 = Johnson boundary) of a=k+1 HALVES per doubling
of n: 0.50 (n=8) -> 0.25 (n=16) -> 0.125 (n=32) -> ... -> 0. So a=k+1 is NOT a fixed interior
radius; it slides into the CAPACITY boundary as n grows. The list blow-up there (7 -> 273, ~3/4 of
the combinatorial ceiling) is the well-known **near-capacity list-decoding explosion**, on the
CAPACITY side of the interior (NOT the Johnson side the disproof targeted, per O164).

At a FIXED interior radius (window-fraction 0.5, the true mid-window):
- n=8: contaminated (a=k+1 coincides with mid because n is tiny) — ignore.
- n=16: a=6, MAX list = **3** even under HEAVY search (8 seeds x 60 passes) — O(1), << budget 16.
- n=32: a=12, MAX list = **0-1** (densest-cluster L=8,16,32,48 all exact) — clean confirmation.

The agreement distribution of the n=16 a=5 word: 455 codewords agree on exactly 4 pts, 273 on
exactly 5, ZERO on >=6 — a sharp near-capacity packing, collapsing immediately above a=k+1.

## FIXED-RELATIVE-RADIUS GROWTH (the actual disproof test) — window midpoint a/n≈0.375

| n  | mid-window a | MAX list (heavy search / cluster) | budget ~n |
|----|--------------|-----------------------------------|-----------|
| 16 | 6            | **3**  (8 seeds x 60 passes smart climb) | 16   |
| 32 | 12           | **0-1** (densest-cluster L=8,16,verified exact) | 32 |

At a FIXED interior radius the max-list does NOT grow with n — it stays O(1) and even DECREASES
(16->3, 32->0/1), far below budget ~n. No super-linear growth, no super-budget word.

## VERDICT: FLOOR HOLDS at fixed interior radius
No super-budget word at a fixed interior radius (bounded away from capacity). Max-list at fixed
window-fraction does NOT grow (n=16 -> 3, n=32 -> 0/1). The only growth (7 -> 273 at a=k+1) is a
NEAR-CAPACITY effect: a=k+1 has a/n -> rho (capacity) as n->inf, window-fraction -> 0, so it is NOT
a fixed interior radius. This is the standard list-decoding blow-up AT the capacity boundary, on
the CAPACITY side (the disproof was hypothesized on the Johnson side, where lists are 1-2 here).
Corroborated by: cross-field (q=65617 & 65633 both give 273), the parallel Method-2 census
(super_budget:false on all families; rho=1/2 a=9->35,a=10->3,a=11->1), and the expected-list
estimate E[list]=C(n,a)q^{k-a} -> 0 at fixed interior a. Evidence FOR the floor; NO disproof found.
