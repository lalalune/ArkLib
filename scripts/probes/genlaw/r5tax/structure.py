#!/usr/bin/env python3
"""Verify the structural bookkeeping identities + forcing lemmas on classes.json,
and emit the tables for DERIVED-99512.md."""
import json, collections
from math import comb

B = 14
cls = json.load(open('/tmp/r5tax/classes.json'))
assert len(cls) == 11808

# ---- axis-type vector bookkeeping ----
# non-z* live types: T1 ('','P') np, T2 ('','O') no, T3 ('O','P') a,
#                    T4 ('O','O') q, T5 ('P','P') p5, T6  ('OP','P') f3
TYPES = {('','P'):'np', ('','O'):'no', ('O','P'):'a', ('O','O'):'q',
         ('P','P'):'p5', ('OP','P'):'f3'}
viol = 0
agg = collections.Counter()
z8_stats = collections.defaultdict(lambda: [0,0])     # z8type -> [classes, ways]
z8_eps   = collections.defaultdict(collections.Counter)
hv_eps   = collections.defaultdict(collections.Counter)
strata_eps = collections.defaultdict(collections.Counter)
q2 = []
e6_at_16_only = True
e4p_z8 = collections.Counter()
permask = collections.Counter()                        # O -> live masks
vec_census = collections.Counter()
for r in cls:
    v = collections.Counter()
    for t in r['sig']:
        v[TYPES[tuple(t)]] += 1
    np_, no_, a_, q_, p5_, f3_ = (v[x] for x in ('np','no','a','q','p5','f3'))
    zl, zh = r['sig8']
    nz_nonempty = sum(v.values())
    E0 = 16 - 1 - nz_nonempty                          # z* axis always nonempty (L)
    t8 = len(zl) + len(zh) + 1                         # +1 = L itself? no: zh includes... L not in occ letters
    # careful: sig8 letters exclude nothing; L IS in zh ('L' included by engine? engine stored occ letters incl 'L')
    # engine put 'L' into occ via terms list -> zh contains 'L'. So t8 = len(zl)+len(zh).
    t8 = len(zl) + len(zh)
    d8 = len(zl) - len(zh)
    # identities
    P8 = zl.count('P') + zh.count('P')
    O8 = zl.count('O') + zh.count('O')
    ok = True
    ok &= (np_ + a_ + 2*p5_ + 2*f3_ + P8 == 10)                       # products
    ok &= (no_ + a_ + 2*q_ + f3_ + O8 == 5)                           # O-terms
    ok &= (r['h'] == np_ + no_ + f3_ + (1 if abs(d8) == 1 else 0))    # forced axes
    ok &= (r['v'] == E0 + p5_ + (1 if r['zfree'] else 0))             # free axes
    ok &= (r['w'] == comb(r['v'], (B - r['h'])//2))
    ok &= abs(d8) <= 1
    if not ok: viol += 1
    key = (np_, no_, a_, q_, p5_, f3_, (zl or '-') + '|' + (zh or '-'), E0)
    vec_census[key] += 1
    z8k = (zl or '-') + '|' + (zh or '-')
    z8_stats[z8k][0] += 1; z8_stats[z8k][1] += r['w']
    z8_eps[z8k][r['eps']] += 1
    hv_eps[(r['h'],r['v'])][r['eps']] += 1
    if q_ == 2: q2.append(r)
    if r['e6'] and 'PP' not in zl: e6_at_16_only = False
    if r['e4p']: e4p_z8[z8k] += 1
    permask[(tuple(r['O']),)] = 0  # placeholder
print(f"identity violations: {viol} / {len(cls)}  (expect 0)")

# q=2 forcing lemma: two E1 pairs => e5>=1 and e6>=1
bad = [r for r in q2 if r['e5'] < 1 or r['e6'] < 1]
print(f"q=2 classes: {len(q2)}; violating (e5>=1 and e6>=1): {len(bad)}  (expect 0)")
print(f"E6 events located only at slot 16 (z* light): {e6_at_16_only}")
print(f"e4p (24 in O) z8 types: {dict(e4p_z8)}")

# per-O live-mask distribution
po = collections.Counter()
for r in cls: po[tuple(r['O'])] += 1
dist = collections.Counter(po.values())
print(f"O-sets with >=1 live mask: {len(po)} of 8736 parity-pure; live-mask multiplicity dist: {dict(sorted(dist.items()))}")

# z8 type table
print("\nz8-type table (type: classes, ways, eps0/eps1 classes):")
tot_c = tot_w = 0
for k, (c, w) in sorted(z8_stats.items(), key=lambda t: -t[1][1]):
    e = z8_eps[k]
    print(f"   {k:8s} classes {c:5d} ways {w:6d}  eps0 {e[0]:5d} eps1 {e[1]:5d}")
    tot_c += c; tot_w += w
print(f"   crossfoot: classes {tot_c} ways {tot_w}")

# (h,v) x eps table
print("\n(h,v) x eps (classes):")
for (h,v), e in sorted(hv_eps.items()):
    print(f"   h={h:2d} v={v:2d}: eps0 {e[0]:5d} eps1 {e[1]:5d}")

# vector census (top granularity node table)
print(f"\ndistinct structural vectors (np,no,a,q,p5,f3,z8,E0): {len(vec_census)}")
agg2 = collections.Counter()
for (np_,no_,a_,q_,p5_,f3_,z8,E0), c in vec_census.items():
    agg2[(a_,q_,p5_,f3_,z8,E0)] += c
print(f"distinct coarse vectors (a,q,p5,f3,z8,E0): {len(agg2)}")

# event-vector x (h,v) consistency: h,v determined by vector?
det = collections.defaultdict(set)
for r in cls:
    v = collections.Counter()
    for t in r['sig']: v[TYPES[tuple(t)]] += 1
    zl, zh = r['sig8']
    key = (v['np'],v['no'],v['a'],v['q'],v['p5'],v['f3'],(zl or '-')+'|'+(zh or '-'))
    det[key].add((r['h'],r['v'],r['w']))
multi = {k: s for k, s in det.items() if len(s) > 1}
print(f"vector keys mapping to multiple (h,v,w): {len(multi)}  (expect 0 => (h,v,w) is a function of the vector)")

# E5=2 relation structure: omitted indices distinct?
import itertools
def e5pairs(O, m):
    a = [O[0]] + [O[i] + 32*((m >> (i-1)) & 1) for i in range(1,5)]
    rel = []
    P = [(i,j,(a[i]+a[j])%64) for i in range(5) for j in range(i+1,5)]
    for x in range(10):
        for y in range(x+1,10):
            if (P[x][2]-P[y][2])%64 == 32 or (P[y][2]-P[x][2])%64 == 32:
                rel.append((set(P[x][:2]), set(P[y][:2])))
    return rel
omit_pat = collections.Counter()
for r in cls:
    if r['e5'] == 2:
        rel = e5pairs(r['O'], r['m'])
        assert len(rel) == 2
        omits = [5*(len(a|b)==4) and (set(range(5))-(a|b)).pop() for a,b in rel]
        omits = [(set(range(5))-(a|b)).pop() for a,b in rel]
        omit_pat['distinct' if omits[0]!=omits[1] else 'same'] += 1
print(f"e5=2 omitted-index pattern: {dict(omit_pat)}  (lemma predicts all distinct)")
