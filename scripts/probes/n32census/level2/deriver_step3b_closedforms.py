"""DERIVER STEP 3b: assert the hand-derived closed forms for every node of the case tree,
and extract the dual-B (multiplicity-4) mechanism for the 92.

u-coordinates: o_i = eps + 2 u_i, T = {u1,u2,u3} subset Z_8, s = sum(T) mod 8.
Closed-form event laws (DERIVED):
  E1  <=>  some pair of T differs by 4
  E2  <=>  3 s mod 8 in T          (kappa2 = 3s; 3 = 3^{-1} mod 8)
  E3  <=>  (s - c3) mod 8 in T,  c3 = 4 - eps
  E4  <=>  eps = 0 and T cap {2,6} nonempty
sigma-count per u-triple = 4 / 2^{#side-constrained P-pairs}  (E2 pair, E3 pair; equal
pair when E2&E3 coincide, which happens iff E4 with the colliding o).
"""
from itertools import combinations
from collections import Counter, defaultdict
import json

# ---------- recompute event pattern for every u-triple, both eps ----------
def events(eps, T):
    s = sum(T) % 8
    E1 = any((b - a) % 8 == 4 for a, b in combinations(T, 2))
    E2 = (3 * s) % 8 in T
    E3 = (s - (4 - eps)) % 8 in T
    E4 = tuple(sorted((eps + 2*u) % 16 for u in T if eps == 0 and u % 4 == 2))
    return E1, E2, E3, E4

pat = defaultdict(list)
for eps in (0, 1):
    for T in combinations(range(8), 3):
        pat[(eps,) + events(eps, T)].append(T)

# ---------- assert the hand-derived u-triple counts ----------
# eps = 1: 56 = 8 x {generic, E1, E2, E3, E1E2, E1E3, E2E3}, E1E2E3 = 0
for key, want in [((1, False, False, False, ()), 8), ((1, True, False, False, ()), 8),
                  ((1, False, True, False, ()), 8), ((1, False, False, True, ()), 8),
                  ((1, True, True, False, ()), 8), ((1, True, False, True, ()), 8),
                  ((1, False, True, True, ()), 8), ((1, True, True, True, ()), 0)]:
    got = len(pat.get(key, []))
    assert got == want, (key, got, want)
print("[3b] eps=1: 56 u-triples = 8 x (generic, E1, E2, E3, E1E2, E1E3, E2E3); E1E2E3 = 0  OK")

# eps = 0 nodes (E4 distinguishes o=4 (u=2) vs o=12 (u=6)):
eps0 = {k[1:]: v for k, v in pat.items() if k[0] == 0}
def n0(e1, e2, e3, e4):
    return len(eps0.get((e1, e2, e3, e4), []))
checks0 = [
    ((False, False, False, ()), 0),     # NO generic triples at eps=0
    ((True, False, False, ()), 4),      # E1 only
    ((False, True, False, ()), 4),      # E2 only
    ((False, False, True, ()), 4),      # E3 only
    ((True, False, True, ()), 4),       # {0,4,t}, t odd  (E1 pair = E3 pair {0,4})
    ((True, True, False, ()), 0),       # E1E2 without E3: empty at eps0
    ((True, True, True, ()), 4),        # the 4 odd triples in {1,3,5,7}
    ((False, True, True, ()), 0),       # E2E3 (different pairs) without E4: empty at eps0
    ((False, False, False, (4,)), 6),   # o=4 only
    ((True, False, False, (4,)), 2),    # {2,1,5}, {2,3,7}
    ((False, True, False, (4,)), 4),    # {2,0,1},{2,0,5},{2,3,4},{2,4,7}
    ((False, True, True, (4,)), 2),     # {2,1,3},{2,5,7}  (E2=E3 pair, o=4 collision)
    ((True, True, True, (4,)), 1),      # {0,2,4}
    ((False, True, True, (12,)), 2),    # {1,3,6},{5,7,6}
    ((True, True, True, (12,)), 1),     # {0,4,6}
    ((False, False, False, (4, 12)), 0),   # both o=4,o=12 => pair {2,6} => E1 auto
]
# triples with both 2,6 (o=4 AND o=12): 6 total, all E1, ALL infeasible (proved):
n46 = sum(len(v) for k, v in eps0.items() if k[3] == (4, 12))
assert n46 == 6
for key, want in checks0:
    got = n0(*key)
    assert got == want, (key, got, want)
# triples containing 6 without E3, and {2,6} triples: infeasible -> count them:
dead = [T for T in combinations(range(8), 3)
        if (2 in T and 6 in T) or (6 in T and 2 not in T and not events(0, T)[2])]
# note: {2,6,t} never satisfies E3 (proved), so the two criteria don't overlap badly
print(f"[3b] eps=0 node counts all match hand derivation; dead u-triples at eps0: "
      f"{len(dead)} (= 6 with o=4&o=12 + 12 with o=12 unrescued) -> 38 live")
assert len(dead) == 18

# ---------- closed-form total ----------
#                cls  = (#u-triples) x sigma_count ; ways = C(v,k)
NODES = [
    # (eps, label, #u, sigma, ways)
    ("e1 generic",            8, 4, 1),
    ("e1 E1",                 8, 4, 2),
    ("e1 E2",                 8, 2, 2),
    ("e1 E3",                 8, 2, 3),
    ("e1 E1E2",               8, 2, 3),
    ("e1 E1E3",               8, 2, 6),
    ("e1 E2E3",               8, 1, 6),
    ("e0 E1",                 4, 4, 2),
    ("e0 E2",                 4, 2, 2),
    ("e0 E3",                 4, 2, 3),
    ("e0 E1E3({0,4}+odd)",    4, 2, 6),
    ("e0 E1E2E3(odd family)", 4, 1, 10),
    ("e0 E4(o4)",             6, 4, 2),
    ("e0 E1+E4(o4)",          2, 4, 3),
    ("e0 E2+E4(o4)",          4, 2, 3),
    ("e0 E2E3+E4(o4) mega",   2, 2, 3),
    ("e0 E1E2E3+E4(o4) mega", 1, 2, 6),
    ("e0 E2E3+E4(o12) mega",  2, 2, 3),
    ("e0 E1E2E3+E4(o12) mega",1, 2, 6),
]
tot = sum(nu * sg * w for _, nu, sg, w in NODES)
ncls = sum(nu * sg for _, nu, sg, w in NODES)
print(f"[3b] closed-form: classes = {ncls}, Sigma classes x C(v,k) = {tot}")
assert tot == 672 and ncls == 232
for name, nu, sg, w in NODES:
    print(f"      {name:26s} {nu:2d} u x {sg} sigma x {w:2d} ways = {nu*sg*w:3d}")

# ---------- dual-B mechanism ----------
recs = json.load(open("/tmp/derive672/class_records.json"))
from math import comb
perB = defaultdict(list)
for r in recs:
    O = tuple(r['O']); sig = tuple(r['sig'])
    forced = set(r['forced']); free = list(r['freeaxes'])
    for pick in combinations(free, r['k']):
        B = frozenset(forced) | {c for c in pick} | {c + 8 for c in pick}
        perB[B].append((O, sig, r['h'], r['v'], r['k']))
dual = {B: v for B, v in perB.items() if len(v) == 2}
print(f"\n[3b] dual B's: {len(dual)}")
mech = Counter()
for B, ((O1, s1, h1, v1, k1), (O2, s2, h2, v2, k2)) in dual.items():
    i = set(O1) & set(O2)
    if len(i) == 0:
        # disjoint: relation between O1 and O2?
        rel = sorted(((o2 - o1) % 16 for o1 in O1 for o2 in O2 if (o2 - o1) % 16 in (4, 8, 12)))
        sh4 = frozenset((o + 4) % 16 for o in O1) == frozenset(O2)
        shm4 = frozenset((o - 4) % 16 for o in O1) == frozenset(O2)
        mech[('disjoint', h1, h2, 'shift4' if (sh4 or shm4) else 'other')] += 1
    else:
        mech[('share2', h1, h2)] += 1
for k, n in sorted(mech.items(), key=lambda t: -t[1]):
    print(f"      {k}  x{n}")

# what labels do dual classes carry?
def lab_of(O, sig):
    eps = O[0] % 2
    T = tuple(sorted((o - eps) // 2 for o in O))
    return (eps,) + events(eps, T)[:3] + (events(eps, T)[3],)
dl = Counter()
for B, pair in dual.items():
    l1, l2 = sorted(str(lab_of(O, s)) for O, s, *_ in pair)
    dl[(l1, l2)] += 1
print("\n[3b] dual-pair label combos:")
for k, n in sorted(dl.items(), key=lambda t: -t[1]):
    print(f"      {k[0]}  <->  {k[1]}   x{n}")
print("DONE")
