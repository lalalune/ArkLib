#!/usr/bin/env python3
"""G5 — the union bound vs the EXACT union, computed by Mobius over the locus universe.
Setup (O94/O95/O96/O129): V_Z = {f : deg f < k=16, both coefficient slices vanish on Z},
|V_Z| = q^(16-2|Z|) exactly for |Z| <= 8 (the O96 bijection; q = BabyBear), V_Z1 ∩ V_Z2 =
V_(Z1 ∪ Z2). The measured cross-pair family: 4,072 distinct loci (subsets of the 16
fibers, sizes 1-7) covering all 47,040 witness-dense differences (O129 dichotomy:
locus = S∩B).
METHOD (exact, no truncation): for D ⊆ [16], g(D) := #{f : dead set ⊇ D} = q^max(0,16-2|D|);
exact(D) := #{f : dead set = D} = superset Mobius of g; |⋃_family V_Z| = Σ exact(D) over
the upward closure of the family. All transforms O(2^16 · 16) on exact big ints.
VERDICT TARGETS: (i) the union-bound sum Σ_Z q^(16-2|Z|) over the 4,072 loci vs the exact
union — the incidence slack factor, exactly; (ii) honest interpretation incl. the
remaining (weight-filter) gap to the 47,040 actual differences."""
import json
from math import comb

q = 2013265921
N = 16
loci = [frozenset(L) for L in json.load(open('/tmp/incidence/cross_loci_cache.json'))['loci']]
fam = set(int(''.join('1' if i in L else '0' for i in range(N)), 2) for L in set(loci))
distinct = len(fam)
sizes = {}
for L in set(loci): sizes[bin(int(''.join('1' if i in L else '0' for i in range(N)), 2)).count('1')] = None
# g over all 2^16 masks
FULL = 1 << N
popc = [bin(m).count('1') for m in range(FULL)]
g = [q**(16 - 2*popc[m]) if 16 - 2*popc[m] > 0 else 1 for m in range(FULL)]
# superset Mobius: exact(m) = sum_{m' superset m} (-1)^{|m'|-|m|} g(m')
# via standard transform: for each bit, f[m] -= f[m | bit] (superset Mobius)
exact = g[:]
for b in range(N):
    bit = 1 << b
    for m in range(FULL):
        if not (m & bit):
            exact[m] -= exact[m | bit]
assert all(e >= 0 for e in exact), "negative exact count — model violated"
assert sum(exact) == q**16, "partition check failed"
# upward closure flags of the family
flag = bytearray(FULL)
for m in fam: flag[m] = 1
for b in range(N):
    bit = 1 << b
    for m in range(FULL):
        if (m & bit) and flag[m ^ bit]: flag[m] = 1
union_exact = sum(exact[m] for m in range(FULL) if flag[m])
union_bound = sum(q**(16 - 2*popc[m]) for m in fam)
print(f"distinct loci: {distinct}; sizes present: {sorted(set(popc[m] for m in fam))}")
print(f"union-bound sum : {union_bound}")
print(f"exact union     : {union_exact}")
ratio = union_bound / union_exact
print(f"slack factor    : {ratio:.6f}")
# per-size leading terms for the report
from collections import Counter
sz = Counter(popc[m] for m in fam)
print(f"loci by size: {dict(sorted(sz.items()))}")
# minimal elements of the family (antichain that drives the union)
minimal = [m for m in fam if not any((m2 != m and (m2 & m) == m2) for m2 in fam)]
print(f"minimal loci (antichain size): {len(minimal)}; by size: {dict(sorted(Counter(popc[m] for m in minimal).items()))}")
mb = sum(q**(16 - 2*popc[m]) for m in minimal)
print(f"union-bound over MINIMAL loci only: {mb} (ratio to exact: {mb/union_exact:.6f})")
print(f"actual differences in the union: 47040 (the weight-filter gap: union/47040 = {union_exact/47040:.3e})")
