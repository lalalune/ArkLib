"""FORECAST VERIFIER, part 2: direct char-0 enumeration at n=64 (s=32), pattern (15,3).

Generic engine (my own implementation of forced/free-axis analysis straight from the
antipodal-balance criterion in Z[zeta_{2s}] = Z[X]/(X^s+1)):
  multiset {x1x2,x1x3,x2x3} u B_z u O_z u {-z*} balanced <=>
    odd axes m: n[m]==n[m+s] outright (B,O,z* terms are all even-exponent);
    even axis c (fiber pair {c, c+s/2}): dd = n[2c]-n[2c+s];
      |dd|>=2 infeasible; dd=+-1 forces a single B on the light side (not in O);
      dd=0: free B-pair axis iff both fibers outside O.
  completions per class = C(v, (|B|-h)/2), |B| = s/2-1.

Calibration inside this very script: s=16 must give 672 classes-sum (proven O108 truth).
Then s=32: the true n=64 count + full strata.
"""
from itertools import combinations
from math import comb
from collections import Counter, defaultdict
import json

SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]

def engine(s, want_sols=False):
    n2 = 2 * s
    msz = s // 2 - 1
    classes = []
    sols = [] if want_sols else None
    mixed_contrib = 0
    for O in combinations(range(s), 3):
        Oset = set(O)
        pure = (O[0] % 2 == O[1] % 2 == O[2] % 2)
        for sig in SIGS:
            d = (0, sig[0], sig[1])
            a = [O[i] + s * d[i] for i in range(3)]
            terms = [(a[0] + a[1]) % n2, (a[0] + a[2]) % n2, (a[1] + a[2]) % n2,
                     (2 * O[0]) % n2, (2 * O[1]) % n2, (2 * O[2]) % n2,
                     (3 * s // 2) % n2]
            cnt = [0] * n2
            for t in terms:
                cnt[t] += 1
            ok = all(cnt[m] == cnt[m + s] for m in range(1, s, 2))
            forced, free = [], []
            if ok:
                for c in range(s // 2):
                    dd = cnt[2 * c] - cnt[2 * c + s]
                    if abs(dd) >= 2:
                        ok = False; break
                    if dd == -1:
                        f = c
                    elif dd == 1:
                        f = c + s // 2
                    else:
                        if c not in Oset and (c + s // 2) not in Oset:
                            free.append(c)
                        continue
                    if f in Oset:
                        ok = False; break
                    forced.append(f)
            if not ok:
                continue
            h, v = len(forced), len(free)
            if (msz - h) < 0 or (msz - h) % 2 or (msz - h) // 2 > v:
                continue
            k = (msz - h) // 2
            w = comb(v, k)
            classes.append(dict(O=O, sig=sig, h=h, v=v, k=k, ways=w,
                                forced=tuple(sorted(forced)), freeaxes=tuple(free),
                                terms=tuple(terms), pure=pure))
            if not pure:
                mixed_contrib += w
            if want_sols:
                for pick in combinations(free, k):
                    B = frozenset(forced) | {c for c in pick} | {c + s // 2 for c in pick}
                    sols.append((B, O, sig))
    return classes, sols, mixed_contrib

# ---- calibration: s=16 must reproduce the PROVEN 672 / 1344 ----------------------
cl16, sols16, mix16 = engine(16, want_sols=True)
tot16 = sum(c['ways'] for c in cl16)
print(f"[CAL s=16] feasible (O,sigma) classes: {len(cl16)}; sum C(v,k) = {tot16}; "
      f"elements = {2 * tot16}; mixed-parity contribution = {mix16}")
assert tot16 == 672 and 2 * tot16 == 1344 and mix16 == 0
BO16 = defaultdict(set)
for B, O, sg in sols16:
    BO16[(B, O)].add(sg)
assert all(len(x) == 1 for x in BO16.values())
Bc16 = Counter(B for B, O, s_ in sols16)
m16 = Counter(Bc16.values())
print(f"[CAL s=16] distinct B = {len(Bc16)}; per-B multiplicity {dict(m16)} "
      f"(expect 580 = 488 x1 + 92 x2)  PASS={len(Bc16)==580 and m16.get(1)==488 and m16.get(2)==92}")
assert len(Bc16) == 580 and m16[1] == 488 and m16[2] == 92

# ---- the target: s=32 (n=64), pattern (15,3) --------------------------------------
cl32, sols32, mix32 = engine(32, want_sols=True)
tot32 = sum(c['ways'] for c in cl32)
print(f"\n[N64] feasible (O,sigma) classes: {len(cl32)}")
print(f"[N64] TRUE char-0 count, pattern (15,3): sum C(v,k) = {tot32} (B,O,sigma) classes")
print(f"[N64] marginal-layer ELEMENT count = 2 x {tot32} = {2 * tot32}")
print(f"[N64] mixed-parity contribution = {mix32} (parity lemma generalizes iff 0)")

# strata
hv = Counter((c['h'], c['v'], c['k']) for c in cl32)
print(f"[N64] (h,v,k) class strata: {dict(sorted(hv.items()))}")
wsum = defaultdict(int)
for c in cl32:
    wsum[(c['h'], c['v'], c['k'])] += c['ways']
print(f"[N64] (h,v,k) -> sum ways: {dict(sorted(wsum.items()))}")

# epsilon split (O = {2u + eps}: parity of the pure O-triple)
eps = Counter()
epsw = defaultdict(int)
for c in cl32:
    e = c['O'][0] % 2
    eps[e] += 1
    epsw[e] += c['ways']
print(f"[N64] parity split: classes {dict(eps)}; ways {dict(epsw)} "
      f"(n=32 analogue was 368 eps=1 + 304 eps=0 = 672)")

# sigma uniqueness per (B,O); B census; dual geometry
BO = defaultdict(set)
for B, O, sg in sols32:
    BO[(B, O)].add(sg)
sigu = Counter(len(x) for x in BO.values())
print(f"[N64] sigma-classes per (B,O): {dict(sigu)} (L5 generalizes iff all 1)")
Bc = Counter(B for B, O, sg in sols32)
mh = Counter(Bc.values())
print(f"[N64] distinct B: {len(Bc)}; (O,sigma)-per-B histogram: {dict(sorted(mh.items()))}")
print(f"[N64] element multiplicity menu per B: "
      f"{{ {', '.join(f'{2*k}: {v}' for k, v in sorted(mh.items()))} }}")
perB = defaultdict(list)
for B, O, sg in sols32:
    perB[B].append(set(O))
dual = {b: o for b, o in perB.items() if len(o) >= 2}
disj = sum(1 for o in dual.values() if len(o) == 2 and not (o[0] & o[1]))
print(f"[N64] B's with >=2 O's: {len(dual)}; disjoint-O pairs among them: {disj}")

# z*-axis slot strata (axis c = s/4 = 8, fiber pair {8, 24}; -z* lives at fiber 24)
def zaxis_type(c):
    n2 = 64
    by = defaultdict(list)
    lab = ['P', 'P', 'P', 'O', 'O', 'O', 'L']
    for t, l in zip(c['terms'], lab):
        by[t].append(l)
    lo = ''.join(sorted(by.get(16, [])))       # exponent 16 = z* slot (fiber 8)
    hi = ''.join(sorted(by.get(48, [])))       # exponent 48 = -z* slot (fiber 24)
    # add forced-B occupancy on this axis
    if 8 in c['forced']:
        lo += 'B'
    if 24 in c['forced']:
        hi += 'B'
    free = 8 in c['freeaxes']
    return '|'.join(sorted([lo, hi])) + ('+free' if free else '')

zs = Counter(zaxis_type(c) for c in cl32)
zw = defaultdict(int)
for c in cl32:
    zw[zaxis_type(c)] += c['ways']
print(f"[N64] z*-axis class strata: {dict(zs)}")
print(f"[N64] z*-axis ways strata: {dict(zw)}")

# witness layer (analytic, same balance law): S = {z*} u (s/4 pairs of s/2-1 axes)
print(f"\n[N64] witness-layer forecast from the same balance law: C(15,8) = {comb(15,8)}")

json.dump([dict(O=c['O'], sig=c['sig'], h=c['h'], v=c['v'], k=c['k'], ways=c['ways'],
                forced=c['forced'], freeaxes=c['freeaxes'], terms=c['terms'])
           for c in cl32], open("/tmp/genlaw/n64_class_records.json", "w"))
json.dump([[sorted(B), list(O), list(sg)] for B, O, sg in sols32],
          open("/tmp/genlaw/n64_sols.json", "w"))
print(f"[OUT] /tmp/genlaw/n64_class_records.json ({len(cl32)} classes), "
      f"n64_sols.json ({len(sols32)} (B,O,sigma) solutions)")
