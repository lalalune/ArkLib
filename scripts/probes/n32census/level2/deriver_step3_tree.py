"""DERIVER STEP 3: analytic case tree for the 232 feasible (O,sigma) classes.

Coordinates: pure parity eps in {0,1}; o_i = eps + 2 u_i, u = {u1<u2<u3} subset Z_8.
Derived axes (Z_8): O-axis(i) = (eps + 2u_i) mod 8;  P-axis(ij) = (eps+u_i+u_j) mod 8
  (P-axes pairwise distinct since u_i distinct; P never collides with a P).
Events (each occurs at most once per class, proved in the note):
  E1: antipodal O-pair  (u_j = u_i + 4)            -> O|O slot, axis blocked for B
  E2: AP condition 2u_k = u_i + u_j (k vs other 2) -> P(ij) on O-axis(k);
      side: p = o_k (same side, INFEASIBLE) or p = o_k + 8 (O|P slot)
  E3: P-axis(ij) = 4 (eps+u_i+u_j = 4 mod 8)       -> P on the L-axis;
      side: p = fiber 4 (pairs L) or p = fiber 12 (INFEASIBLE, proved)
  E4: o on axis 4 (eps=0, u in {2,6}; o in {4,12}) -> O on the L-axis
      o = 4: O|L slot (L fixed by the O-term);  o = 12: needs E3 to repair (mega slot)
Each feasible class: h forced B-fibers (light sides), v free axes, k=(7-h)/2,
ways = C(v,k).  This script groups classes by event label and prints the tree,
then ASSERTS the closed-form binomial count for every node.
"""
import json
from collections import Counter, defaultdict
from itertools import combinations
from math import comb

recs = json.load(open("/tmp/derive672/class_records.json"))
assert len(recs) == 232


def label(rec):
    O = tuple(rec['O']); s12, s13, s23 = rec['sig']
    eps = O[0] % 2
    u = tuple((o - eps) // 2 for o in O)
    d = (0, s12, s13)
    a = [O[i] + 16 * d[i] for i in range(3)]
    pexps = {(0, 1): (a[0]+a[1]) % 32, (0, 2): (a[0]+a[2]) % 32, (1, 2): (a[1]+a[2]) % 32}
    # E1
    pairs = [(i, j) for i, j in combinations(range(3), 2) if (u[j]-u[i]) % 8 == 4]
    E1 = pairs[0] if pairs else None
    # E2: 2u_k = u_i+u_j (mod 8), k the singleton
    E2 = None
    for k in range(3):
        i, j = [t for t in range(3) if t != k]
        if (u[i]+u[j] - 2*u[k]) % 8 == 0:
            pe = pexps[(i, j)]
            E2 = (k, 'same' if pe == (2*O[k]) % 32 else 'opp')
    # E3: P-axis = 4
    E3 = None
    for (i, j), pe in pexps.items():
        if (pe % 16) == 8:
            E3 = ((i, j), 'f4' if pe == 8 else 'f12')   # fiber 4 (exp 8) or 12 (exp 24)
    # E4: o in {4,12}
    E4 = tuple(sorted(o for o in O if o % 8 == 4))
    return eps, u, (('E1', E1 is not None),
                    ('E2', E2[1] if E2 else None),
                    ('E3', E3[1] if E3 else None),
                    ('E4', E4))


groups = defaultdict(list)
for r in recs:
    eps, u, lab = label(r)
    groups[(lab, r['h'], r['v'], r['k'])].append((eps, u, tuple(r['sig']), r))

print(f"{'label (E1,E2,E3,E4)':58s} {'h':>2} {'v':>2} {'k':>2} {'#cls':>4} {'C(v,k)':>6} {'subtot':>6}")
total = 0
rows = []
for key in sorted(groups, key=lambda t: (-len(groups[t]), t[1])):
    lab, h, v, k = key
    n = len(groups[key])
    w = comb(v, k)
    assert all(r['ways'] == w for _, _, _, r in groups[key])
    total += n * w
    rows.append((lab, h, v, k, n, w))
    print(f"{str(lab):58s} {h:2d} {v:2d} {k:2d} {n:4d} {w:6d} {n*w:6d}")
print(f"TOTAL = {total}")
assert total == 672

# ---------------- per-eps split for closed forms ----------------
print("\nper-(eps,label) class counts:")
ge = defaultdict(Counter)
for key, lst in groups.items():
    for eps, u, sig, r in lst:
        ge[key][eps] += 1
for key in sorted(ge, key=lambda t: str(t[0])):
    lab, h, v, k = key
    print(f"  {str(lab):58s} eps0:{ge[key][0]:3d}  eps1:{ge[key][1]:3d}")

# ---------------- u-triple level (sigma collapsed) ----------------
print("\nper-label distinct u-triples (eps0/eps1) and sigma-multiplicity:")
gu = defaultdict(lambda: defaultdict(set))
for key, lst in groups.items():
    for eps, u, sig, r in lst:
        gu[key[0]][eps].add((u, sig))
for lab in sorted(gu, key=str):
    for eps in (0, 1):
        pairs = gu[lab][eps]
        uts = Counter(u for u, s in pairs)
        if pairs:
            print(f"  {str(lab):58s} eps{eps}: {len(uts)} u-triples, "
                  f"sigma-per-u {dict(Counter(uts.values()))}")
