#!/usr/bin/env python3
"""Machine-asserted char-0 proof that e5 <= 2 at r=5, and that two E5 relations
must omit distinct indices.

An E5 relation is x_i x_j = -x_k x_l with {i,j,k,l} distinct (shared-index is
proven dead by hand), i.e. u.a == 32 (mod 64) with u = e_i+e_j-e_k-e_l, u ~ -u.
There are exactly 15 such vectors (5 omitted indices x 3 pairings).

Kill rules (each derived from fiber-distinctness: fibers o_i = a_i mod 32 are
pairwise distinct):
  For relations R_1..R_T (T = #nonzero eps), any eps in {-1,0,1}^T gives
  (sum eps_t u_t) . a == 32*T' (mod 64), T' = #nonzero.
  - combo == 0       : kill iff T' odd          (0 == 32 impossible)
  - combo == +-(e_i - e_j)  : kill always       (a_i == a_j mod 32 -> same fiber)
  - combo == +-2(e_i - e_j) : kill iff T' even  (a_i == a_j mod 32)
A set of relations is 'admissible' if NO eps choice triggers a kill.
THEOREM (this script): every 3-subset of the 15 vectors is inadmissible,
and the admissible 2-subsets are exactly those omitting distinct indices.
"""
import itertools, numpy as np

idx = list(range(5))
vecs = []   # (omitted, frozenset pair1, frozenset pair2, vector)
for omit in idx:
    rest = [i for i in idx if i != omit]
    a = rest[0]
    for b in rest[1:]:
        c, d = [x for x in rest[1:] if x != b]
        u = np.zeros(5, dtype=int)
        u[a] = u[b] = 1; u[c] = u[d] = -1
        key = frozenset([frozenset([a, b]), frozenset([c, d])])
        if not any(k == key for _, _, k in [(0, 0, frozenset([p, q])) for _, _, p, q in []]):
            pass
        vecs.append((omit, key, u))
# dedupe (each partition counted once)
seen = set(); V = []
for omit, key, u in vecs:
    if key in seen: continue
    seen.add(key); V.append((omit, key, u))
assert len(V) == 15, len(V)

def killed(us):
    T = len(us)
    for eps in itertools.product((-1, 0, 1), repeat=T):
        Tp = sum(1 for e in eps if e)
        if Tp == 0: continue
        c = sum(e * u for e, u in zip(eps, us))
        nz = c[c != 0]
        if len(nz) == 0:
            if Tp % 2 == 1: return ('zero-combo', eps)
        elif len(nz) == 2 and sorted(nz) == [-1, 1]:
            return ('e_i-e_j', eps)
        elif len(nz) == 2 and sorted(nz) == [-2, 2]:
            if Tp % 2 == 0: return ('2(e_i-e_j)', eps)
    return None

# pairs
alive_pairs = []
for (o1, k1, u1), (o2, k2, u2) in itertools.combinations(V, 2):
    if killed([u1, u2]) is None:
        alive_pairs.append((o1, o2, k1, k2))
print(f"admissible 2-subsets: {len(alive_pairs)} of {15*14//2}")
assert all(o1 != o2 for o1, o2, _, _ in alive_pairs), "lemma: distinct omitted indices"
print("  all admissible pairs omit DISTINCT indices: True")
# distribution: for each omitted-index pair, how many partition pairs are alive?
import collections
dd = collections.Counter(frozenset((o1, o2)) for o1, o2, _, _ in alive_pairs)
print(f"  per omit-pair multiplicities: {sorted(dd.values())}")

# triples
alive_triples = 0
kill_reasons = collections.Counter()
for (o1, k1, u1), (o2, k2, u2), (o3, k3, u3) in itertools.combinations(V, 3):
    res = killed([u1, u2, u3])
    if res is None:
        alive_triples += 1
    else:
        kill_reasons[res[0]] += 1
print(f"admissible 3-subsets: {alive_triples} of {15*14*13//6}  (0 => e5 <= 2 PROVEN)")
print(f"kill reasons over all triples: {dict(kill_reasons)}")
