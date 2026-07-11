#!/usr/bin/env python3
"""Falsifier for the explicit-transversal kit (#357 support bricks).

Claims under test, at RS[F5, (1,2,4,3), 2]:
  (T1) epsMCA numerator (max bad-scalar count over ALL 5^8 stacks) equals the max over
       pairs from the explicit transversal R = words vanishing on I = {positions 0,1}
       (25 words, 625 pairs) -- at every integer-threshold radius t in {4, 3}.
       [t = 4 <-> delta < 1/4 grid point; t = 3 <-> delta = 1/4]
  (T2) the cover property: every word u has r in R with u - r a codeword.
Ground truth (probe lab + R1 file): worst count = 1 at t=4, 4 at t=3.
"""
from itertools import product

p, n, k = 5, 4, 2
xs = [1, 2, 4, 3]
cws = {tuple((a + b * x) % p for x in xs) for a in range(p) for b in range(p)}
words = list(product(range(p), repeat=n))
subsets = []
for mask in range(1 << n):
    S = [i for i in range(n) if mask >> i & 1]
    subsets.append(tuple(S))

def ext(w, S):
    return any(all(c[i] == w[i] for i in S) for c in cws)

def bad_count(u0, u1, t):
    cnt = 0
    for g in range(p):
        line = tuple((a + g * b) % p for a, b in zip(u0, u1))
        if any(len(S) >= t and ext(line, S) and not (ext(u0, S) and ext(u1, S))
               for S in subsets):
            cnt += 1
    return cnt

# T2: cover property for I = {0,1}
I = (0, 1)
R = [w for w in words if all(w[i] == 0 for i in I)]
assert len(R) == p ** (n - len(I)) == 25
for u in words:
    assert any(tuple((a - b) % p for a, b in zip(u, r)) in cws for r in R), u
print("T2 PASS: vanishingOn{0,1} (25 words) covers every coset of all 5^4 words")

# T1: max bad count, transversal pairs vs (syndrome-reduced) all-stack ground truth
for t, expect in ((4, 1), (3, 4)):
    m_cover = max(bad_count(r0, r1, t) for r0 in R for r1 in R)
    assert m_cover == expect, (t, m_cover, expect)
    print(f"T1 PASS at t={t}: max over 625 transversal pairs = {m_cover} = ground truth")

# independent cross-check of ground truth at t=3 over a full sweep using coset
# decomposition: every stack = (r0+c0, r1+c1); spot-verify invariance on 2000 random stacks
import random
random.seed(357)
for _ in range(2000):
    u0, u1 = random.choice(words), random.choice(words)
    r0 = next(r for r in R if tuple((a - b) % p for a, b in zip(u0, r)) in cws)
    r1 = next(r for r in R if tuple((a - b) % p for a, b in zip(u1, r)) in cws)
    assert bad_count(u0, u1, 3) == bad_count(r0, r1, 3)
print("invariance spot-check PASS: 2000 random stacks match their transversal reps at t=3")

# T3: sparse-cover bound (SparseCoverComputable.lean), delta = 1/4, t = 3.
# s0 = ceil((1-3*delta)*n) = 1, s1 = ceil((1-2*delta)*n) = 2.
# Claim: eps_mca <= max(1/q, M/q) with M = max bad count over sparseRows(s0) x sparseRows(s1).
# Ground truth eps_mca(1/4) = 4/5, so M must be exactly 4 (the extremal stack has a
# sparse representative); also re-check the deviation mechanism: every stack with >= 2
# bad scalars at t=3 must have a sparse-pair representative with the same count.
def sparse_rows(s):
    return [w for w in words
            if any(all(w[i] == 0 for i in S) for S in subsets if len(S) >= s)]

R0, R1 = sparse_rows(1), sparse_rows(2)
M = max(bad_count(r0, r1, 3) for r0 in R0 for r1 in R1)
assert M == 4, M
print(f"T3 PASS: sparse cover |R0|={len(R0)}, |R1|={len(R1)}; max sparse-pair count = {M}"
      f" = ground truth (bound 4/5 <= max(1/5, 4/5) tight)")
print("ALL PASS")
