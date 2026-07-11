"""DERIVER STEP 3c: explicit dual-B matching rules for the disjoint families."""
import json
from itertools import combinations
from collections import Counter, defaultdict

recs = json.load(open("/tmp/derive672/class_records.json"))
perB = defaultdict(list)
for r in recs:
    O = tuple(r['O']); sig = tuple(r['sig'])
    forced = frozenset(r['forced']); free = list(r['freeaxes'])
    for pick in combinations(free, r['k']):
        B = frozenset(forced) | {c for c in pick} | {c + 8 for c in pick}
        perB[B].append((O, sig, forced, tuple(sorted(pick)), r['h']))

def fam(O1, O2):
    i = set(O1) & set(O2)
    return 'share2' if i else 'disjoint'

ex = defaultdict(list)
for B, v in perB.items():
    if len(v) == 2:
        (O1, s1, f1, p1, h1), (O2, s2, f2, p2, h2) = v
        key = (fam(O1, O2), h1, h2)
        ex[key].append((B, v))

for key in sorted(ex, key=str):
    print(f"\n===== family {key}  x{len(ex[key])} =====")
    for B, ((O1, s1, f1, p1, h1), (O2, s2, f2, p2, h2)) in ex[key][:6]:
        print(f"  B={sorted(B)}")
        print(f"    O1={O1} sig{s1} forced={sorted(f1)} pick={p1}")
        print(f"    O2={O2} sig{s2} forced={sorted(f2)} pick={p2}")
        # relations
        d = sorted(((o2 - o1) % 16) for o1, o2 in zip(O1, O2))
        print(f"    O2-O1 (sorted componentwise) = {d}; O1+4={sorted((o+4)%16 for o in O1)}; "
              f"O1+8={sorted((o+8)%16 for o in O1)}; 3*O1={sorted((3*o)%16 for o in O1)}; "
              f"5*O1={sorted((5*o)%16 for o in O1)}")
