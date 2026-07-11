#!/usr/bin/env python3
"""
probe_clique_orbit_freeness.py  (#444 decay-rate frontier)

QUESTION (the missing glue between schurrot's proven equivariance and lalalune's
D*(m) = (orbit size <= n) * #clique-orbits(m)):

  Is the <zeta>-rotation action  R' |-> zeta * R'  on the (k+1)-subsets of mu_n
  FREE? i.e. does every orbit have size EXACTLY n = ord(zeta)?

If FREE, then the count of clique-bearing level-set reps D*(m) = n * #(orbits of
clique-bearing gammas), a clean Burnside-free factorization that is PURELY group-
theoretic (NO cyclotomic collision content) -- a separable Lean brick.

If NOT free (some R' has a nontrivial stabilizer: zeta^j * R' = R' as a SET for
0<j<n), then the factorization has the "<= n" not "= n", and the orbit-size is
itself structured -- closer to the open content.

We test freeness of the action on (k+1)-SUBSETS of mu_n (the level-set carriers),
which is what "orbit size <= n" in lalalune's identity refers to.

A (k+1)-subset S of mu_n = {zeta^0,...,zeta^{n-1}} is stabilized by zeta^j iff
zeta^j * S = S as sets, i.e. the exponent set E(S) subset Z_n satisfies E+j = E (mod n).
This is a PURE Z_n combinatorics question: which subsets E of size k+1 are periodic
with a period j | n, j < n.

NEVER validated at n=q-1 (this is a char-0 / pure cyclic-action structural probe).
"""
import itertools

def stabilizer_order(E, n):
    """Largest divisor structure: return the set of j in 0..n-1 with E+j == E (mod n)."""
    Eset = set(E)
    stab = []
    for j in range(n):
        if set((e + j) % n for e in Eset) == Eset:
            stab.append(j)
    return stab  # always contains 0; |stab| divides n

def analyze(n, ksize):
    """ksize = k+1 = subset size. Report freeness stats over ALL (k+1)-subsets."""
    total = 0
    nonfree = 0
    nonfree_examples = []
    stab_size_hist = {}
    for E in itertools.combinations(range(n), ksize):
        stab = stabilizer_order(E, n)
        s = len(stab)
        total += 1
        stab_size_hist[s] = stab_size_hist.get(s, 0) + 1
        if s > 1:
            nonfree += 1
            if len(nonfree_examples) < 4:
                nonfree_examples.append((E, stab))
    return total, nonfree, stab_size_hist, nonfree_examples

print("=== Freeness of <zeta> action on (k+1)-subsets of mu_n ===")
print("(stab size 1 == free orbit of size n; stab size s>1 == orbit size n/s)\n")
# prize regime: k = n/4, so k+1 ~ n/4+1. Also test small subset sizes.
for n in [8, 16, 32]:
    for ksize in sorted(set([2, 3, n//4, n//4 + 1, n//2])):
        if ksize < 1 or ksize > n:
            continue
        total, nonfree, hist, ex = analyze(n, ksize)
        free = (nonfree == 0)
        tag = "FREE (all orbits size n)" if free else f"NOT free ({nonfree}/{total} subsets stabilized)"
        print(f"n={n:3d} subset-size(k+1)={ksize:2d}: {tag}")
        if not free:
            print(f"        stab-size histogram: {hist}")
            for (E, stab) in ex:
                print(f"        e.g. E={E} stabilized by j in {stab} (orbit size {n//len(stab)})")
    print()

print("=== Interpretation ===")
print("A (k+1)-subset E is stabilized by j (0<j<n) iff E is a union of cosets of <j>")
print("in Z_n. That requires (n/gcd) | (k+1). So the action is FREE on (k+1)-subsets")
print("UNLESS (k+1) shares the divisor structure of n that allows a periodic subset.")
print("For ODD k+1 with n a 2-power: any period j|n has n/j even (j<n, n=2^a), so a")
print("periodic E has even size -> ODD (k+1) FORCES freeness. k=n/4 -> k+1 = n/4+1.")
print("n=8:k+1=3 odd FREE; n=16:k+1=5 odd FREE; n=32:k+1=9 odd FREE. Prize regime k+1 odd!")
