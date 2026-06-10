"""DERIVER STEP 2: pure combinatorial enumerator over Z[zeta_32] exponents (NO field arithmetic).

Object: solutions of  e2(x1,x2,x3) + e1(B_z) + e1(O_z) - z* = 0  with
  x_i = zeta^{o_i + 16 d_i}  (fiber o_i in Z_16, sign d_i in {0,1}),
  B subset Z_16, |B| = 7, disjoint from O = {o1,o2,o3}, z* = zeta^8 (fiber 4),
  -z* = zeta^24 (fiber 12).
The equation is a vanishing sum of 14 elements of mu_32; in the power basis
{zeta^0..zeta^15} (zeta^16 = -1) vanishing  <=>  for every axis m in Z_16:
  #terms at exponent m  ==  #terms at exponent m+16   ("antipodal balance").

Enumeration: over ALL O in C(16,3) x 4 sigma-classes (including mixed parity, to
PROVE mixed parity contributes 0), B placed by the forced/free-axis rule:
  per even axis (fiber-pair {c, c+8}): d = n[2c]-n[2c+16] (n = non-B terms);
    |d|>=2 -> infeasible; |d|=1 -> B forced on light side (must not be in O);
    d=0 -> free for a B-pair iff c,c+8 both not in O.
  odd axes: B cannot help -> need n[m]==n[m+16] outright.
Then #B-completions = C(v, (7-h)/2).

Cross-checks against the measured data census:
  * total (B,O,sigma) = 672; x2 global sign = 1344
  * EXACT set equality with /tmp/derive672/data_sols.json
  * per-(B,O) sigma-uniqueness; B-census 580 = 488 x1(O) + 92 x2(O); dual-O geometry
  * slot-type histogram == data class_type_hist (19 types)
"""
import json
from itertools import combinations
from math import comb
from collections import Counter, defaultdict

SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]   # (s12,s13,s23), s12^s13^s23=0

sols = []            # (B(frozen), O(tuple), sig(tuple))
class_records = []   # per-(O,sigma): structural record for step 3
infeasible_mixed = 0
feasible_mixed = 0

for O in combinations(range(16), 3):
    o1, o2, o3 = O
    pure = (o1 % 2 == o2 % 2 == o3 % 2)
    for sig in SIGS:
        s12, s13, s23 = sig
        d = (0, s12, s13)                       # delta representative
        a = [O[i] + 16 * d[i] for i in range(3)]  # zeta-exponents of x_i
        # 7 non-B terms as zeta-exponents
        terms = [(2 * o1) % 32, (2 * o2) % 32, (2 * o3) % 32,
                 (a[0] + a[1]) % 32, (a[0] + a[2]) % 32, (a[1] + a[2]) % 32,
                 24]
        n = [0] * 32
        for t in terms:
            n[t] += 1
        Oset = set(O)
        feasible = True
        forced = []
        freeaxes = []
        for m in range(1, 16, 2):               # odd axes: B cannot contribute
            if n[m] != n[m + 16]:
                feasible = False
                break
        if feasible:
            for c in range(8):                  # even axis = fiber pair {c, c+8}
                dd = n[2 * c] - n[(2 * c + 16) % 32]
                if abs(dd) >= 2:
                    feasible = False
                    break
                if dd == -1:
                    f = c
                elif dd == 1:
                    f = c + 8
                else:
                    if c not in Oset and (c + 8) not in Oset:
                        freeaxes.append(c)
                    continue
                if f in Oset:
                    feasible = False
                    break
                forced.append(f)
        h = len(forced)
        v = len(freeaxes)
        if feasible and (7 - h) >= 0 and (7 - h) % 2 == 0 and (7 - h) // 2 <= v:
            k = (7 - h) // 2
            ways = comb(v, k)
            for pick in combinations(freeaxes, k):
                B = frozenset(forced) | {c for c in pick} | {c + 8 for c in pick}
                assert len(B) == 7 and not (B & Oset)
                sols.append((B, O, sig))
            class_records.append(dict(O=O, sig=sig, h=h, v=v, k=k, ways=ways,
                                      forced=tuple(sorted(forced)),
                                      freeaxes=tuple(freeaxes), terms=tuple(terms)))
            if not pure:
                feasible_mixed += ways
        else:
            if not pure:
                infeasible_mixed += 1

print(f"[E] total (B,O,sigma) solutions: {len(sols)}   (x2 global sign = {2*len(sols)})")
print(f"[E] mixed-parity O contributions: {feasible_mixed} (lemma L1: must be 0)")
assert feasible_mixed == 0

# ---- exact set equality with the data census ----
data = json.load(open("/tmp/derive672/data_sols.json"))
dset = {(frozenset(B), tuple(O), tuple(s)) for B, O, s in data}
eset = {(B, O, s) for B, O, s in sols}
print(f"[E] data (B,O,sigma) classes: {len(dset)}; enumerator: {len(eset)}; "
      f"EQUAL: {dset == eset}")
assert dset == eset

# ---- per-(B,O) sigma uniqueness ----
BO = defaultdict(set)
for B, O, s in sols:
    BO[(B, O)].add(s)
assert all(len(v) == 1 for v in BO.values())
print(f"[E] distinct (B,O): {len(BO)}; sigma-classes per (B,O): all 1 (L5 confirmed)")

# ---- B census ----
Bcnt = Counter(B for B, O, s in sols)
mh = Counter(Bcnt.values())
print(f"[E] distinct B: {len(Bcnt)}; (O,sigma)-per-B histogram: {dict(sorted(mh.items()))} "
      f"(elements per B = 2x: {{2: {mh.get(1,0)}, 4: {mh.get(2,0)}}})")

# ---- dual geometry ----
perB = defaultdict(list)
for B, O, s in sols:
    perB[B].append(set(O))
geo = Counter()
for B, Os in perB.items():
    if len(Os) == 2:
        i = Os[0] & Os[1]
        np1 = sum(1 for t in Os[0] if (t + 8) % 16 in Os[0]) // 2
        np2 = sum(1 for t in Os[1] if (t + 8) % 16 in Os[1]) // 2
        if len(i) == 0:
            geo[('disjoint', np1, np2)] += 1
        else:
            ip = frozenset((t + 8) % 16 for t in i) == frozenset(i)
            c1 = next(iter(Os[0] - i)); c2 = next(iter(Os[1] - i))
            geo[('share', len(i), 'pair' if ip else 'nonpair',
                 (c2 - c1) % 16 if len(i) == 2 else None)] += 1
print(f"[E] dual-O geometry: {dict(geo)}")

# ---- slot-type census (same convention as data census.py) ----
def slot_type(B, O, sig):
    s12, s13, s23 = sig
    d = (0, s12, s13)
    a = [O[i] + 16 * d[i] for i in range(3)]
    terms = [((a[0] + a[1]) % 32, 'P'), ((a[0] + a[2]) % 32, 'P'),
             ((a[1] + a[2]) % 32, 'P'), (24, 'L')]
    terms += [((2 * z) % 32, 'B') for z in B]
    terms += [((2 * z) % 32, 'O') for z in O]
    by = defaultdict(list)
    for e, c in terms:
        by[e].append(c)
    slots = []
    for m in range(16):
        ca, cb = sorted(by.get(m, [])), sorted(by.get(m + 16, []))
        assert len(ca) == len(cb)
        if ca or cb:
            slots.append('|'.join(sorted([''.join(ca), ''.join(cb)])))
    return tuple(sorted(slots))

tcensus = Counter(slot_type(B, O, s) for B, O, s in sols)
ref = json.load(open("/tmp/derive672/summary.json"))["class_type_hist"]
refc = {tuple(sorted(k.split(' ; '))): v for k, v in ref.items()}
print(f"[T] enumerator class-type histogram == data class_type_hist: "
      f"{dict(tcensus) == refc}  ({len(tcensus)} types)")
assert dict(tcensus) == refc

json.dump([dict(O=r['O'], sig=r['sig'], h=r['h'], v=r['v'], k=r['k'],
                ways=r['ways'], forced=r['forced'], freeaxes=r['freeaxes'],
                terms=r['terms']) for r in class_records],
          open("/tmp/derive672/class_records.json", "w"))
print(f"[OUT] {len(class_records)} feasible (O,sigma) classes -> class_records.json")
print(f"[SUM] Sigma C(v,k) over feasible (O,sigma) = {sum(r['ways'] for r in class_records)}")
print("STEP2 DONE")
