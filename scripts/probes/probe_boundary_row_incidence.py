#!/usr/bin/env python3
"""Probe: the boundary-row (d = 2b-1) bad census is a LINE-BLOCK INCIDENCE count.

PRE-REGISTERED QUESTION (issue #357, 26-program item 1 second half + item 18 at f=0):
the band-3 sweep at (17,8,4), d = 5 = 2b-1 found a stack with >= 6 bad scalars, while
the pencil supply gives only n/(b-1) = 4.  What is the extra mechanism, and what is the
true maximum?

MODEL.  At the boundary row m = n-k = 2(b-1) (f = 0), a weight-(b-1) error word on a
block B has twisted-syndrome vector in R_B := {syndromes of P/V_B : deg P <= b-2}, a
(b-1)-dim subspace of F^m (codim b-1).  A stack with bad scalars {gam_a} on blocks
{B_a} is an affine line L = {s0 + gam*s1} in syndrome space with L(gam_a) in R_{B_a}.
The bad census of the stack is (up to the MCA no-joint filter) the INCIDENCE COUNT of
the line with the union of all C(n, b-1) block subspaces -- NOT just a pencil family.

HYPOTHESES:
  H1: lines exist hitting strictly more than n/(b-1) blocks (explains the sweep's 6).
  H2: the maximum incidence over all lines is what the sweep measured (= the exact
      boundary-row value at this cell), and the maximizer geometry identifies the
      extra mechanism beyond the equal-sum/coset pencil.

METHOD.  (17, mu_8, k=4), b=3, m=4, blocks = all 28 pairs {i,j}.
R_{ij} = span of synd(delta_i-type fractions): explicitly, syndromes s_t = sum over
block of w_x x^t for free weights w -> R_ij = span{(1,x_i,x_i^2,x_i^3)*eta_i-ish}.
We use untwisted error syndromes directly: e supported on {i,j} with weights (w_i,w_j)
has syndrome sum_x w_x*eta_x*(1,x,x^2,x^3).  So R_ij = span{c_i, c_j} with
c_x = eta_x*(1,x,x^2,x^3).

Enumerate lines through (p1 in R_B1 projective, p2 in R_B2 full), B1 < B2; for each
other block solve the 2-condition linear system for gamma; count consistent admissible
(both weights nonzero) incidences.  Then verify the top stacks END-TO-END at the
mcaEvent level (independent engine: support enumeration + per-row interpolability).
"""

import itertools
from fractions import Fraction

p = 17
g = 2
xs = [pow(g, i, p) for i in range(8)]
n, k, m, b = 8, 4, 4, 3

def inv(a): return pow(a % p, p - 2, p)

eta = []
for i in range(n):
    pr = 1
    for l in range(n):
        if l != i: pr = (pr * (xs[i] - xs[l])) % p
    eta.append(inv(pr))

def col(i):
    return [(eta[i] * pow(xs[i], t, p)) % p for t in range(m)]

cols = [col(i) for i in range(n)]
blocks = list(itertools.combinations(range(n), 2))

def solve2(c1, c2, target):
    """solve a*c1 + b*c2 = target (vectors in F^m); return (a,b) or None; also detect
    non-uniqueness (shouldn't happen: c1, c2 independent)."""
    # use first two independent coordinate rows
    for r1 in range(m):
        for r2 in range(r1 + 1, m):
            det = (c1[r1] * c2[r2] - c1[r2] * c2[r1]) % p
            if det:
                a = ((target[r1] * c2[r2] - target[r2] * c2[r1]) * inv(det)) % p
                bb = ((c1[r1] * target[r2] - c1[r2] * target[r1]) * inv(det)) % p
                # verify all rows
                for r in range(m):
                    if (a * c1[r] + bb * c2[r] - target[r]) % p: return None
                return (a, bb)
    return None

def incidences(s0, s1):
    """all (block, gamma, weights) with s0 + gamma*s1 in R_block, weights nonzero."""
    out = []
    for (i, j) in blocks:
        ci, cj = cols[i], cols[j]
        # solve s0 + gamma*s1 = a*ci + b*cj : 4 equations, unknowns (gamma, a, b)
        # eliminate: for each pair of rows build linear system; brute over gamma is 17 ops
        for gam in range(p):
            t = [(s0[r] + gam * s1[r]) % p for r in range(m)]
            sol = solve2(ci, cj, t)
            if sol and sol[0] and sol[1]:
                out.append(((i, j), gam, sol))
    return out

# ---------- stage 1: line enumeration via block-pair anchors ----------
# projective reps of R_B1: a*ci + b*cj with (a,b) in {(1,t): t in F} u {(0,1)}
best = []
seen_lines = set()
import random
random.seed(357)

def line_key(s0, s1):
    # canonicalize under (s0,s1) -> (s0 + c*s1, a*s1): use frozenset of points on line
    pts = frozenset(tuple((s0[r] + gam * s1[r]) % p for r in range(m)) for gam in range(p))
    return pts

count_hist = {}
B1B2 = list(itertools.combinations(range(len(blocks)), 2))
for (bi1, bi2) in B1B2:
    (i1, j1), (i2, j2) = blocks[bi1], blocks[bi2]
    c11, c12 = cols[i1], cols[j1]
    c21, c22 = cols[i2], cols[j2]
    reps1 = [(1, t) for t in range(p)] + [(0, 1)]
    for (a1, b1) in reps1:
        if not a1 and not b1: continue
        p1 = [(a1 * c11[r] + b1 * c12[r]) % p for r in range(m)]
        # skip degenerate weight-zero anchors
        if not a1 or not b1: continue
        # p2 sampled: full enumeration is 289; take all with both weights nonzero
        for a2 in range(1, p):
            for b2 in range(1, p):
                p2 = [(a2 * c21[r] + b2 * c22[r]) % p for r in range(m)]
                s1v = [(p2[r] - p1[r]) % p for r in range(m)]
                if all(v == 0 for v in s1v): continue
                inc = incidences(p1, s1v)
                cnt = len(set(x[0:2] for x in inc))
                # count distinct gammas (the bad census candidate)
                gams = set(x[1] for x in inc)
                cg = len(gams)
                count_hist[cg] = count_hist.get(cg, 0) + 1
                if cg >= 6:
                    key = line_key(p1, s1v)
                    if key not in seen_lines:
                        seen_lines.add(key)
                        best.append((cg, p1, s1v, inc))
        # full sweep is 378 * 18 * 256 * 28 * 17 too slow in python; subsample anchors
        break  # one anchor rep per (B1,B2) pair: (1,1)-anchored; rely on line transitivity
    if len(best) > 400: break

best.sort(key=lambda x: -x[0])
print("histogram of distinct-gamma incidence counts (sampled lines):",
      dict(sorted(count_hist.items())))
print("top line incidence counts:", [x[0] for x in best[:10]])

# ---------- stage 2: end-to-end mcaEvent verification of the top stacks ----------
def interpolable(pts, vals):
    rows = [[pow(x, jj, p) for jj in range(k)] + [v % p] for x, v in zip(pts, vals)]
    nr = len(rows); r = 0
    for c in range(k):
        piv = next((i for i in range(r, nr) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        ivv = inv(rows[r][c])
        rows[r] = [(a * ivv) % p for a in rows[r]]
        for i in range(nr):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * bb) % p for a, bb in zip(rows[i], rows[r])]
        r += 1
    return all(not (all(a == 0 for a in row[:-1]) and row[-1] != 0) for row in rows)

def word_from_synd(s):
    """word supported on first m coords with given twisted syndrome."""
    rows = [[(eta[i] * pow(xs[i], t, p)) % p for i in range(m)] + [s[t]] for t in range(m)]
    for c in range(m):
        piv = next(i for i in range(c, m) if rows[i][c])
        rows[c], rows[piv] = rows[piv], rows[c]
        ivv = inv(rows[c][c])
        rows[c] = [(a * ivv) % p for a in rows[c]]
        for i in range(m):
            if i != c and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * bb) % p for a, bb in zip(rows[i], rows[c])]
    return [rows[i][m] for i in range(m)] + [0] * (n - m)

def exact_bad_set(u0, u1, agree_floor):
    bad = []
    idx = list(range(n))
    max_err = n - agree_floor
    for gam in range(p):
        y = [(u0[i] + gam * u1[i]) % p for i in range(n)]
        found = False
        for esz in range(0, max_err + 1):
            for E in itertools.combinations(idx, esz):
                Sc = [i for i in idx if i not in E]
                pts = [xs[i] for i in Sc]
                if not interpolable(pts, [y[i] for i in Sc]): continue
                ok0 = interpolable(pts, [u0[i] for i in Sc])
                ok1 = interpolable(pts, [u1[i] for i in Sc])
                if not (ok0 and ok1):
                    found = True
                    break
            if found: break
        if found: bad.append(gam)
    return bad

print("\n=== end-to-end mcaEvent verification of top candidate stacks ===")
agree_floor = n - (b - 1)  # = 6, delta*n = 2 (band 3)
verified_max = 0
for (cg, s0v, s1v, inc) in best[:6]:
    u1 = word_from_synd(s1v)
    u0 = word_from_synd(s0v)
    bad = exact_bad_set(u0, u1, agree_floor)
    verified_max = max(verified_max, len(bad))
    pencil_like = sorted(set(x[1] for x in inc))
    print(f"line-incidence {cg} (gammas {pencil_like}) -> EXACT mcaEvent bad set "
          f"{bad} (count {len(bad)})")
    blocksets = sorted(set(x[0] for x in inc))
    print(f"   blocks hit: {blocksets}")

print(f"\nVERDICT: max verified bad count at the boundary row (17,8,4) delta*n=2: "
      f"{verified_max} (pencil supply = 4 = n/(b-1))")
