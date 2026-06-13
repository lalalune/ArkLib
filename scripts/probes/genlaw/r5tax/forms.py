#!/usr/bin/env python3
"""Closed-form lemma layer + node-accounting verification for r=5, s=32."""
from itertools import combinations
from math import comb
from collections import Counter, defaultdict
import json

M = 16
CL = json.load(open('/tmp/r5tax/classes.json'))
print(f"loaded {len(CL)} classes")

# ---------- Lemma C1: E1 census (antipodal pairs {u,u+8} in U) ----------
# closed form: N_j = C(8,j) C(8-j, 5-2j) 2^(5-2j)
form = {j: comb(8, j) * comb(8 - j, 5 - 2 * j) * 2 ** (5 - 2 * j) for j in (0, 1, 2)}
cnt = Counter()
for U in combinations(range(M), 5):
    s = set(U); j = sum(1 for u in U if (u + 8) % M in s) // 2
    cnt[j] += 1
print("C1 E1-census: closed form", form, " direct", dict(cnt),
      " OK" if form == dict(cnt) else " MISMATCH")
assert form == dict(cnt)

# ---------- Lemma C2: lambda-pair census, pi=1 (pairs {u, 7-u}) ----------
cnt = Counter()
for U in combinations(range(M), 5):
    s = set(U); t = sum(1 for u in U if (7 - u) % M in s and (7 - u) % M != u) // 2
    cnt[t] += 1
print("C2 lam-census pi=1: closed form", form, " direct", dict(cnt),
      " OK" if form == dict(cnt) else " MISMATCH")
assert form == dict(cnt)

# ---------- Lemma C3: lambda census pi=0: a = |U cap {4,12}|, t = #pairs {u,8-u} ----------
def NC3(a, t):
    rem = 5 - a - 2 * t
    if rem < 0: return 0
    return comb(2, a) * comb(7, t) * comb(7 - t, rem) * 2 ** rem
cnt = Counter()
for U in combinations(range(M), 5):
    s = set(U); a = len(s & {4, 12})
    t = sum(1 for u in U if (8 - u) % M in s and (8 - u) % M != u and u not in (4, 12)) // 2
    cnt[(a, t)] += 1
ok = all(NC3(a, t) == cnt.get((a, t), 0) for a in range(3) for t in range(3))
print("C3 lam-census pi=0 N(a,t):", {k: NC3(*k) for k in sorted(cnt)}, " direct",
      dict(sorted(cnt.items())), " OK" if ok else " MISMATCH")
assert ok and sum(cnt.values()) == comb(16, 5)

# ---------- Lemma A (node accounting): h = 16-X-F, v = X+G, k = (X+F-2)/2 ----------
def xfg(node):
    pi, lam, off = node
    X = F = G = 0
    for ev in off:
        tags = ev.split(':')[0]
        X += len(tags) - 1
        if ev.endswith(':b'):
            F += 1
            if tags == 'PP': G += 1
    lo, hi = lam.split('|')
    m = len(lo) + len(hi)          # includes L
    X += m - 1
    d = len(lo) - len(hi)
    if d == 0:
        F += 1
        if 'O' not in lo + hi: G += 1
    return X, F, G
bad = 0
for c in CL:
    X, F, G = xfg((c['node'][0], c['node'][1], tuple(c['node'][2])))
    if c['h'] != 16 - X - F or c['v'] != X + G or c['k'] != (X + F - 2) // 2 \
       or (X + F - 2) % 2:
        bad += 1
print("Lemma A (accounting h=16-X-F, v=X+G, k=(X+F-2)/2) violations:", bad)
assert bad == 0

# ---------- Lemma V (vocabulary completeness over feasible classes) ----------
OFF_VOCAB = {'DD:b', 'DP:b', 'PP:b', 'DPP:f0', 'DPP:f1'}
LAM_VOCAB = {'|L', 'P|L', 'PP|L', 'P|LP', 'O|L', 'OP|L', 'P|LO', 'OP|LO',
             'PP|LO', 'OP|LP'}
offs = set(); lams = set()
for c in CL:
    lams.add(c['node'][1]); offs.update(c['node'][2])
print("off-lambda vocabulary:", sorted(offs), " == proven set:", offs == OFF_VOCAB)
print("lambda vocabulary:", sorted(lams), " == proven set:", lams == LAM_VOCAB)
assert offs == OFF_VOCAB and lams == LAM_VOCAB

# ---------- E5 derivation: per-node E5 = #PP:b + #DPP + [lam has P both sides] ----------
def e5_of(node):
    _, lam, off = node
    lo, hi = lam.split('|')
    return sum(1 for ev in off if ev == 'PP:b' or ev.startswith('DPP')) + \
           (1 if 'P' in lo and 'P' in hi else 0)
bad = sum(1 for c in CL if c['e5'] != e5_of((c['node'][0], c['node'][1], tuple(c['node'][2]))))
print("E5-from-signature violations:", bad); assert bad == 0
e5c = Counter(c['e5'] for c in CL)
print("E5 census:", dict(sorted(e5c.items())))
assert dict(e5c) == {0: 3768, 1: 7880, 2: 160}

# ---------- strata derivation from node table ----------
nodes = defaultdict(lambda: [0, None])
for c in CL:
    key = (c['node'][0], c['node'][1], tuple(c['node'][2]))
    nodes[key][0] += 1
    hvk = (c['h'], c['v'], c['k'])
    assert nodes[key][1] in (None, hvk)     # node rows are (h,v,k)-pure
    nodes[key][1] = hvk
strata = Counter()
MAP = {'|L': 'B|L', 'O|L': 'L|O', 'OP|L': 'BL|OP', 'P|LO': 'BP|LO',
       'PP|L': 'BL|PP', 'P|LP': 'BP|LP', 'OP|LO': 'LO|OP', 'PP|LO': 'LO|PP',
       'OP|LP': 'LP|OP'}
for (pi, lam, off), (ncl, (h, v, k)) in nodes.items():
    if lam == 'P|L':     # free balanced lambda-axis: placement split
        strata['L|P'] += ncl * comb(v - 1, k)
        strata['BL|BP'] += ncl * (comb(v - 1, k - 1) if k else 0)
    else:
        strata[MAP[lam]] += ncl * comb(v, k)
TARGET = {'L|P':23024,'BL|BP':22720,'B|L':14208,'BL|OP':12032,'BL|PP':10896,
          'L|O':7264,'BP|LO':4480,'BP|LP':2496,'LO|OP':1600,'LO|PP':504,'LP|OP':288}
print("strata from node table:", dict(strata.most_common()))
print("matches target:", dict(strata) == TARGET); assert dict(strata) == TARGET

# ---------- eps decomposition ----------
wpi = Counter(); cpi = Counter()
for c in CL: wpi[c['pi']] += c['ways']; cpi[c['pi']] += 1
print("eps: ways pi0", wpi[0], "pi1", wpi[1], "delta", wpi[0] - wpi[1],
      "| classes", dict(cpi))

# lambda-sector marginals per pi (ways)
lsec = defaultdict(int)
for c in CL: lsec[(c['pi'], c['node'][1])] += c['ways']
print("lambda-sector ways:", {k: v for k, v in sorted(lsec.items())})

# ---------- event marginal censuses over feasible classes ----------
for name, f in [('E1 (DD:b)', lambda off: off.count('DD:b')),
                ('E2 (DP:b)', lambda off: off.count('DP:b')),
                ('E5off (PP:b)', lambda off: off.count('PP:b')),
                ('DPP', lambda off: sum(1 for e in off if e.startswith('DPP')))]:
    print(f"  {name} census:", dict(sorted(Counter(f(c['node'][2]) for c in CL).items())))

# ---------- geometric exclusion check: DDPP axis impossible (Lemma X) ----------
# direct: for all U, no axis carries 2 doubles + 2 disjoint products
viol = 0
for U in combinations(range(M), 5):
    ax = defaultdict(lambda: [0, 0])
    for u in U: ax[(2 * u) % M][0] += 1
    for (i, j) in combinations(range(5), 2):
        ax[(U[i] + U[j]) % M][1] += 1
    for c, (nd, np_) in ax.items():
        if nd >= 2 and np_ >= 2: viol += 1
print("Lemma X (no DD+PP axis geometrically): violations", viol); assert viol == 0
# also: 3 doubles or 3 products on one axis never occur
viol = 0
for U in combinations(range(M), 5):
    ax = defaultdict(lambda: [0, 0])
    for u in U: ax[(2 * u) % M][0] += 1
    for (i, j) in combinations(range(5), 2):
        ax[(U[i] + U[j]) % M][1] += 1
    for c, (nd, np_) in ax.items():
        if nd >= 3 or np_ >= 3: viol += 1
print("Lemma I (max 2 doubles / 2 products per axis): violations", viol)
assert viol == 0
print("ALL FORMS GATES PASS")
