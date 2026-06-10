#!/usr/bin/env python3
"""Issue #232 — probe: the Lam-Leung NN-SPAN law at three squarefree primes (Stage 4).

CLAIM (Lam-Leung J. Algebra 224 (2000) Thm 4.1/5.2, the positive theorem surviving
the O105 refutation): for an NN-weighted vanishing sum on the Z_p x Z_q x Z_r grid,
the TOTAL weight lies in NN*p + NN*q + NN*r.

Content boundary measured first:
  * if {2,3} is a subset of {p,q,r}: NN*2+NN*3 = NN \\ {1}, so the law degenerates to
    "total != 1" (a single root of unity is nonzero) — TRIVIAL at n = 30, 42, 66.
  * first genuinely open shape: all primes odd, e.g. (3,5,7): the Frobenius gaps of
    NN*3+NN*5+NN*7 are {1,2,4} — the law says NO vanishing NN-sum has total 1, 2 or 4.

Checks (exact integer arithmetic):
  1. gap arithmetic: NN*3+NN*5+NN*7 misses exactly {1,2,4} below 40;
     NN*2+NN*3 misses exactly {1}.
  2. at (3,5,7) (n = 105): NO NN-vanishing weight with total 1, 2 or 4 —
     total 1: all 105 unit cells are nonvanishing;
     total 2: all C(105+1,2) = 5565 pair multisets nonvanishing;
     total 4: meet-in-middle over pair-multiset reduced sums (any 4-multiset splits
     into two 2-multisets): no pair-sum s with -s also a pair-sum.  EXHAUSTIVE.
  3. positive controls: full p-, q-, r-packets vanish (totals 3, 5, 7 achieved),
     so the spanned totals are realized.
  4. the OBSTRUCTION record for the formalization: the O105 witness at n = 30 sits
     in the HARD branch of the LL induction — its p=2 slices at level qr = 15 have
     equal NONZERO evaluations (c != 0), so the "all threads vanish, recurse" case
     does not apply; and the per-(j,k) min-shift is identically 0 (no reduction).

Exit 0 iff all checks pass.
"""

import itertools
import sys

FAIL = []


def check(name, ok):
    print(("PASS" if ok else "FAIL"), name)
    if not ok:
        FAIL.append(name)


# ------------------------------------------------------------------ gap arithmetic

def span_gaps(gens, bound):
    reach = {0}
    for _ in range(bound):
        reach |= {x + g for x in reach for g in gens if x + g <= bound}
    return [t for t in range(bound + 1) if t not in reach]


check("NN*3+NN*5+NN*7 gaps below 40 are exactly {1,2,4}",
      span_gaps([3, 5, 7], 40) == [1, 2, 4])
check("NN*2+NN*3 gaps are exactly {1} (the {2,3}-divisible triviality)",
      span_gaps([2, 3], 40) == [1])

# --------------------------------------------------- reduced cell vectors at (3,5,7)

p, q, r = 3, 5, 7
N = p * q * r
DIM = (p - 1) * (q - 1) * (r - 1)


def axis_vec(x, n):
    # coefficients of zeta^x on basis 1..zeta^{n-2} after zeta^{n-1} -> -(sum)
    v = [0] * (n - 1)
    if x < n - 1:
        v[x] = 1
    else:
        v = [-1] * (n - 1)
    return v


CELLS = []
for i in range(p):
    for j in range(q):
        for k in range(r):
            a, b, c = axis_vec(i, p), axis_vec(j, q), axis_vec(k, r)
            vec = tuple(a[x] * b[y] * c[z]
                        for x in range(p - 1) for y in range(q - 1) for z in range(r - 1))
            CELLS.append(vec)

check("(3,5,7) total 1: every unit cell is NONvanishing",
      all(any(v) for v in CELLS))

pair_sums = {}
ok2 = True
for a in range(N):
    for b in range(a, N):
        s = tuple(x + y for x, y in zip(CELLS[a], CELLS[b]))
        if not any(s):
            ok2 = False
        pair_sums.setdefault(s, []).append((a, b))
check("(3,5,7) total 2: all 5565 pair multisets NONvanishing", ok2)

ok4 = True
witness4 = None
for s in pair_sums:
    neg = tuple(-x for x in s)
    if neg in pair_sums:
        ok4 = False
        witness4 = (pair_sums[s][0], pair_sums[neg][0])
        break
check("(3,5,7) total 4: no vanishing quadruple (meet-in-middle, exhaustive)", ok4)
if witness4:
    print("    counterexample cells:", witness4)

# positive controls: packets vanish
def cell_idx(i, j, k):
    return (i * q + j) * r + k

for (label, cells, tot) in [
        ("p-packet (total 3)", [cell_idx(i, 1, 2) for i in range(p)], 3),
        ("q-packet (total 5)", [cell_idx(2, j, 4) for j in range(q)], 5),
        ("r-packet (total 7)", [cell_idx(1, 3, k) for k in range(r)], 7)]:
    s = [0] * DIM
    for c in cells:
        s = [x + y for x, y in zip(s, CELLS[c])]
    check(f"(3,5,7) {label} vanishes", not any(s) and len(cells) == tot)

# --------------------------------------------- the obstruction record at n = 30

print("--- LL induction obstruction: O105 witness at n = 30, threads along p = 2 ---")
S = {5, 6, 12, 18, 24, 25}
# grid coords (i,j,k) = (e%2, e%3, e%5); slice i at level qr = 15
W = {}
for e in range(30):
    W[(e % 2, e % 3, e % 5)] = 1 if e in S else 0

def reduce_2d(M, q, r):
    T = [[M[(j, k)] for k in range(r)] for j in range(q)]
    T = [[T[j][k] - T[q - 1][k] for k in range(r)] for j in range(q - 1)]
    T = [[T[j][k] - T[j][r - 1] for k in range(r - 1)] for j in range(q - 1)]
    return [x for row in T for x in row]

slice0 = {(j, k): W[(0, j, k)] for j in range(3) for k in range(5)}
slice1 = {(j, k): W[(1, j, k)] for j in range(3) for k in range(5)}
diff = {(j, k): slice0[(j, k)] - slice1[(j, k)] for j in range(3) for k in range(5)}
check("witness slices have EQUAL evaluations at level 15 (difference vanishes)",
      not any(reduce_2d(diff, 3, 5)))
check("witness slice evaluation c is NONZERO (the hard LL branch realized)",
      any(reduce_2d(slice0, 3, 5)))
minshift = {(j, k): min(W[(0, j, k)], W[(1, j, k)]) for j in range(3) for k in range(5)}
check("witness per-(j,k) min-shift is identically 0 (no naive reduction available)",
      all(v == 0 for v in minshift.values()))
tot0, tot1 = sum(slice0.values()), sum(slice1.values())
print(f"    slice totals: T_0 = {tot0}, T_1 = {tot1}; total = {tot0 + tot1} = 2*1 + ... "
      f"in NN*2+NN*3+NN*5 via 6 = 3+3 (NOT via the slice split 4+2)")

print()
if FAIL:
    print("FAILURES:", FAIL)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
