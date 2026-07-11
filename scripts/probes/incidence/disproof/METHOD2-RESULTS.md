# Method 2 — structured-construction lists on the proximity window (thin non-Fermat regime)

Lane: nubs disproof seat. Task: take the campaign's STRUCTURED candidate bad words (coset-unions,
e2=0 over-determined census words, subfield/Frobenius words, and the canonical line/max-fiber
witness word), compute their EXACT list AND radius, place them on the window-INTERIOR
(rho*n < a < sqrt(rho)*n), and report whether any lands a SUPER-BUDGET (> ~n) list that GROWS
faster than n across n = 8, 16, 32. Budget = q*eps* ~ n in the prize regime. Falsify-first.

## Setup (thin prize regime, beta = log_n(q) ~ 4, q prime, n | q-1, NON-Fermat)
- n=8:  q = 4129     (in-tree; beta 4.004)
- n=16: q = 65617    (next non-Fermat prime > 65537 with q == 1 mod 16; beta 4.000; NOT 2^k+1)
- n=32: q = 1048609  (~2^20, q == 1 mod 32, non-Fermat; beta 4.000)
mu_n = order-n multiplicative subgroup; RS[F_q, mu_n, k], rho = k/n.
list(w,a) = #{deg<k codewords agreeing with w on >= a points}.  delta = 1 - a/n.

## Tooling (all EXACT modular arithmetic; verified)
- `fastlist.py` exact list counter — self-tested vs `maxlist_core.list_size_exact` (OK at all n<=16).
- `lineword_n32.c` — (K+1)-subset functional-sweep C kernel for the line word at n=32, our thin q.
  CALIBRATION GATE PASSED: at n=16 / step2 / canonical lambda it reproduces the in-tree C19 ground
  truth BIT-EXACTLY: list = 19 = 16 (dense, agree-9) + 3 (witnesses, agree-10). Independent of the
  Python counter (different algorithm). Also reproduces 35 at n=16/step1/lam=1 (matches Python).
- `fast_maxlist_compare.py` — Method-1 cross-family max (random + monomials + O163 densest-cluster
  sweep + line-word lambda sweep), exact, to confirm the line word is EXTREMAL at the interior.

## Construction families built and measured (rho=1/2 and rho=1/4)
(a) COSET-UNION words (constant-on-mu_d-coset, coset indicators, codeword-on-coset-union) — O158.
(b) e2=0 OVER-DETERMINED census words (overlay/union of e2=0 t-cores) — the #bad~n^2/4 family.
(c) SUBFIELD / FROBENIUS words (subgroup indicators, quadratic character, square map, small alphabet).
(d) LINE / MAX-FIBER WITNESS word  w_i = x_i^{k+step} + lambda * x_i^k  (the n32census object).

Families (a),(b),(c) at rho in {1/4,1/2}, n in {8,16}: EVERY one has max-interior list <= 3
(<< budget n). They do NOT land a super-budget interior list. The randomized-complement realizations
host essentially ONE codeword plus chance agreements — the supply-wall e-symm fiber count does NOT
translate into an actual list (the cores do not host DISTINCT codewords against a single word).

The only family that produces a large interior list is (d), the canonical line / max-fiber witness
word — which is the SAME object the n32census measured. Method-1 cross-family search confirms (d)
is EXTREMAL: at n=16, rho=1/2, no random / monomial / densest-cluster word beats the line word at
ANY interior radius (a=9:35, a=10:3, a=11:1 — all by the line/monomial word).

## THE GROWTH TABLE — max-list (over all families) at window-INTERIOR radii, rho=1/2, budget ~ n

| n  | q       | a  | frac=a/n | max-list | budget~n | > n ? | list/n |
|----|---------|----|----------|----------|----------|-------|--------|
| 8  | 4129    | 5  | 0.6250   | 3        | 8        | no    | 0.375  |
| 16 | 65617   | 9  | 0.5625   | 35       | 16       | YES   | 2.188  |
| 16 | 65617   | 10 | 0.6250   | 3        | 16       | no    | 0.188  |
| 16 | 65617   | 11 | 0.6875   | 1        | 16       | no    | 0.062  |
| 32 | 1048609 | 18 | 0.5625   | 35       | 32       | YES   | 1.094  |
| 32 | 1048609 | 20 | 0.6250   | 0        | 32       | no    | 0.000  |

(n=32 a=20: all 35 codewords found at a=18 agree at EXACTLY 18, so list at a>=19 = 0.)

## GROWTH at FIXED interior fraction (the decisive diagnostic)
The interior window's LOWEST integer radius drifts toward capacity (f -> 0.5+) as n grows, and the
list is naturally large just above capacity. The honest growth test fixes the FRACTION f = a/n.

- f = 0.5625 (the witness band, just above capacity), canonical-lambda step2 word (n32census object):
    n=16 -> list 19    n=32 -> list 35      ratio-to-n: 1.19 -> 1.09  (DECREASING)
  => grows ~ n (slightly SUBLINEAR). NOT faster than n. (matches n32census Entry-11 / H3' growth.)

- f = 0.5625, step1 line word X^{k+1}+lam X^k:
    n=16 -> 35         n=32 -> 0            => COLLAPSES (lambda=1 is not the n=32 max-fiber e1).

- f = 0.6250 (mid-window, away from capacity):
    n=8 -> 3     n=16 -> 3     n=32 -> 0    => FLAT-to-DECREASING, far below budget n.

- f = 0.6875 (upper interior, toward Johnson):
    n=16 -> 1                               => trivial.

## VERDICT — FLOOR HOLDS (no disproof signal)
No structured word — coset-union, e2=0 census, subfield/Frobenius, or the extremal line/max-fiber
witness — produces an interior-radius list that GROWS faster than ~n. The only super-budget interior
lists occur at the single radius CLOSEST to capacity (f=0.5625), and there the list grows SUBLINEARLY
(19 -> 35 from n=16 to n=32, ratio-to-n falling 1.19 -> 1.09) — i.e. it tracks ~ n (the n32census
"polynomial-consistent, far below every budget line" finding), not faster. At every interior fraction
bounded away from capacity the list is flat-to-decreasing and far below budget. The e-symm SUPPLY WALL
(max-fiber = 35) does NOT translate into a super-budget ACTUAL list with growth; it equals ~n.

This is EVIDENCE FOR the proximity floor conjecture in the thin non-Fermat regime, not against it.
Honest scope: rho in {1/4,1/2}; n in {8,16,32}; the structured families above + Method-1 cross-family
extremality check at n<=16. Not an exhaustive search over ALL F_q^n words at n=32 (only the structured
+ extremal-confirmed families); but the line word is the family-extremal word at every interior radius
checked, and it does not grow super-budget.

## Reproduce
    python3 fastlist.py                                  # exact-counter self-test
    python3 method2_structured.py --n 16 --q 65617 --rho 0.25     # families (a)(b)(c)
    python3 growth_table.py --rho 0.5                            # line-word growth n=8,16
    python3 fast_maxlist_compare.py --q 65617 --n 16 --rho 0.5   # cross-family extremality
    gcc -O3 -march=native -DQ=1048609 -DGEN=57211 -DNN=32 -DKK=16 -DELO=16 -DEHI=18 \
        -DLAM=1013299 -DAA=18 lineword_n32.c -o lw32
    for i in $(seq 0 15); do ./lw32 $i c$i.txt & done; wait    # ~7 min, 8 cores
    cat c*.txt | sort -u | wc -l                                 # = 35 (n=32 interior list)
