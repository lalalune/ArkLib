#!/usr/bin/env python3
"""INCIDENCE LABORATORY — difference-loci on the proven-complete list configurations
(scope claimed #232 2026-06-10, complement of lalalune lane 2: dense layers, slice
spread of differences, cross-level persistence, union-bound loss on dense mass).

INPUT: raw census kernel rows (values on H), e.g. regenerated via
  gcc -O3 -march=native scripts/probes/n32census/census_kernel.c -o census32
  for i in $(seq 0 15); do ./census32 $i out_$i.txt & done; wait
  python3 probe_incidence.py 'out_*.txt'
This consumes the RAW sweep (not the level-2 TSV distillation) — independent of the
anatomy pipeline end to end.

PRE-REGISTERED HYPOTHESES (stated before first run; verdicts in RESULTS-INCIDENCE.md):
H-INC1 (extra agreements): |Z0(c-c')| > |T cap T'| for a positive fraction of pairs.
H-INC2 (spread blindness): both cross and dense-dense differences are branch-maximal
  at depths 1-3 for >=99% of pairs.
H-INC3 (locus sharing): distinct level-1 dead loci across cross pairs is far below the
  pair count, multiplicity menu echoing the {2,4} structure.
H-INC4 (persistence): n=16 vs n=32 dense-side incidence agrees in shape, not rigidly.

HARD GATES: n=16 sweep reproduces 19=3+16 (witnesses agree-10 all-even); n=32 raw rows
distill to exactly the 35 constructed witnesses (bit-exact) + 1,344 dense (agree exactly
17, deg<16, distinct).
"""
import sys, glob, random
from itertools import combinations
from collections import Counter

P = 2013265921; G0 = 31; LAM = 284861408
def pw(b, e): return pow(b, e, P)
INV = lambda a: pow(a, P-2, P)

def pmul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[i+j] = (out[i+j] + x*y) % P
    return out
def peval(c, x):
    r = 0
    for co in reversed(c): r = (r*x + co) % P
    return r
def interp(xs, ys):
    n = len(xs); out = [0]*n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = pmul(num, [(-xs[j]) % P, 1])
            den = den * ((xs[i]-xs[j]) % P) % P
        s = ys[i] * INV(den) % P
        for d in range(len(num)): out[d] = (out[d] + s*num[d]) % P
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out
def digcode(e, depth):
    ds = []
    for _ in range(depth):
        d = e & 1; ds.append(d); e = (e + d) >> 1
    return tuple(ds)
def spread_of(c, depth):
    supp = [j for j, co in enumerate(c) if co]
    return len({digcode(e, depth) for e in supp})

# ---------- PART 1: n=16 calibration (independent sweep) ----------
def calibrate_n16():
    n, k, A = 16, 8, 9
    h = pw(G0, (P-1)//n)
    H = [pw(h, i) for i in range(n)]
    w = [(pw(x, 10) + LAM*pw(x, 8)) % P for x in H]
    found = {}
    for sub in combinations(range(n), A):
        c = interp([H[i] for i in sub], [w[i] for i in sub])
        if len(c) <= k:
            key = tuple(c + [0]*(k-len(c)))
            if key not in found:
                found[key] = frozenset(i for i in range(n) if peval(list(key), H[i]) == w[i])
    return H, w, found

H16, w16, found16 = calibrate_n16()
wit16 = {c: a for c, a in found16.items() if len(a) == 10}
den16 = {c: a for c, a in found16.items() if len(a) == 9}
even16 = sum(1 for c in wit16 if all(co == 0 for j, co in enumerate(c) if j % 2 == 1))
gate1 = (len(found16) == 19 and len(wit16) == 3 and len(den16) == 16 and even16 == 3)
print(f"GATE n=16: list={len(found16)} = {len(wit16)}+{len(den16)}, wit-even={even16} -> {'PASS' if gate1 else 'FAIL'}")
if not gate1: sys.exit(1)

# ---------- PART 2: n=32 — construct witnesses; distill dense from raw rows ----------
h32 = pw(G0, (P-1)//32); H32 = [pw(h32, i) for i in range(32)]
G16 = [pw(h32*h32 % P, i) for i in range(16)]
w32 = [(pw(x, 18) + LAM*pw(x, 16)) % P for x in H32]
zstar = (P - LAM) % P; zidx = G16.index(zstar)
otherpairs = [(i, i+8) for i in range(8) if i != zidx % 8]
witnesses = {}
for ch in combinations(otherpairs, 4):
    S = [zstar] + [G16[i] for pr in ch for i in pr]
    u = interp(S, [(pw(s, 9) + LAM*pw(s, 8)) % P for s in S])
    assert len(u) <= 8
    c = [0]*16
    for j, co in enumerate(u): c[2*j] = co
    key = tuple(c)
    ag = frozenset(i for i in range(32) if peval(list(key), H32[i]) == w32[i])
    assert len(ag) == 18
    witnesses[key] = ag
assert len(witnesses) == 35

raw_lines = 0
rows = set()
pats = sys.argv[1:] if len(sys.argv) > 1 else ['/tmp/incidence/regen/c17_*.txt']
for pat in pats:
    for f in sorted(glob.glob(pat)):
        for line in open(f):
            raw_lines += 1
            rows.add(tuple(map(int, line.split())))
print(f"raw kernel rows: {raw_lines} lines (functional passes), {len(rows)} distinct value-vectors")
HINV = [INV(x) for x in H32]; inv32 = INV(32)
def idft(vals):
    return tuple(sum(vals[i]*pw(HINV[i], d) for i in range(32)) % P * inv32 % P for d in range(32))
dense = {}; wit_seen = set()
for vals in rows:
    cs = idft(list(vals))
    assert all(co == 0 for co in cs[16:]), "deg >= 16 candidate"
    key = cs[:16]
    ag = frozenset(i for i in range(32) if vals[i] == w32[i])
    if len(ag) >= 18:
        assert key in witnesses and witnesses[key] == ag
        wit_seen.add(key)
    elif len(ag) == 17:
        if key in dense: assert dense[key] == ag
        dense[key] = ag
    else:
        raise AssertionError(f"row with agreement {len(ag)} < 17 emitted")
gate2 = (wit_seen == set(witnesses) and len(dense) == 1344)
acct = f"pass-accounting: {raw_lines} raw (expect 1974 = 35*18 + 1344 when both layers swept)"
print(f"GATE n=32: witnesses {len(wit_seen)}/35 bit-exact, dense={len(dense)}, {acct} -> {'PASS' if gate2 else 'FAIL'}")
if not gate2: sys.exit(1)

# ---------- PART 3: measurements ----------
WIT = list(witnesses.items()); DEN = list(dense.items())
def diff_stats(c1, a1, c2, a2, H):
    d = [(x-y) % P for x, y in zip(c1, c2)]
    Z0 = frozenset(i for i in range(len(H)) if peval(d, H[i]) == 0)
    half = len(H)//2; q = len(H)//4
    L1 = frozenset(i for i in range(half) if (i in Z0 and (i+half) in Z0))
    L2 = frozenset(i for i in range(q) if all((i + j*q) in Z0 for j in range(4)))
    return len(Z0), len(a1 & a2), L1, L2, tuple(spread_of(d, dd) for dd in (1, 2, 3))

def run_block(pairsrc, label):
    eL1 = Counter(); ex = Counter(); sp = Counter(); s1 = Counter(); s2 = Counter()
    npairs = 0
    for (k1, a1), (k2, a2) in pairsrc:
        z0, tt, L1, L2, spp = diff_stats(list(k1), a1, list(k2), a2, H32)
        ex[z0-tt] += 1; eL1[L1] += 1; s1[len(L1)] += 1; s2[len(L2)] += 1; sp[spp] += 1
        npairs += 1
    print(f"\n== {label} ({npairs} pairs) ==")
    print(f"extra-agreement hist: {dict(sorted(ex.items()))}")
    print(f"L1 dead-fiber sizes: {dict(sorted(s1.items()))}")
    print(f"L2 dead-fiber sizes: {dict(sorted(s2.items()))}")
    print(f"distinct L1 loci: {len(eL1)}; mean multiplicity {npairs/max(1,len(eL1)):.2f}; top {eL1.most_common(3)}")
    print(f"locus multiplicity menu (FULL): {dict(sorted(Counter(eL1.values()).items()))}")
    print(f"empty-locus pairs: {eL1.get(frozenset(), 0)}")
    print(f"spread hist (FULL): {dict(sp.most_common())}")
    return eL1, sp

cross_src = ((wv, dv) for wv in WIT for dv in DEN)
crossL1, crossSP = run_block(cross_src, "CROSS 35x1344")
random.seed(20260610)
idxpairs = set()
while len(idxpairs) < 12000:
    i, j = random.randrange(1344), random.randrange(1344)
    if i < j: idxpairs.add((i, j))
ddL1, ddSP = run_block(((DEN[i], DEN[j]) for i, j in sorted(idxpairs)), "DENSE-DENSE sample 12000")
# identify sub-maximal-spread exceptions and extra-agreement pairs explicitly
def neg_poly_t(c): return tuple((co if j % 2 == 0 else (P-co) % P) for j, co in enumerate(c))
print("\n== DENSE-DENSE exception identification ==")
for i, j in sorted(idxpairs):
    (k1, a1), (k2, a2) = DEN[i], DEN[j]
    z0, tt, L1, L2, spp = diff_stats(list(k1), a1, list(k2), a2, H32)
    isneg = (tuple(k2) == neg_poly_t(k1))
    if spp != (2, 4, 8):
        print(f"  sub-maximal pair ({i},{j}): spread {spp}, negation-pair={isneg}")
    if z0 != tt:
        d = [(a-b) % P for a, b in zip(k1, k2)]
        extras = [t for t in range(32) if peval(d, H32[t]) == 0 and not (t in a1 and t in a2)]
        print(f"  extra-agreement pair ({i},{j}): |Z0|-|TcapT'|={z0-tt}, extra idx {extras}, negation-pair={isneg}")

# n=16 reference for persistence
def diff16(c1, a1, c2, a2):
    d = [(x-y) % P for x, y in zip(c1, c2)]
    Z0 = frozenset(i for i in range(16) if peval(d, H16[i]) == 0)
    L1 = frozenset(i for i in range(8) if (i in Z0 and (i+8) in Z0))
    return len(Z0), len(a1 & a2), L1
print(f"\n== n=16 REFERENCE ==")
for label, src in [("cross 3x16", [(wv, dv) for wv in wit16.items() for dv in den16.items()]),
                   ("dense-dense 120", list(combinations(den16.items(), 2)))]:
    ex = Counter(); eL1 = Counter(); s1 = Counter()
    for (k1, a1), (k2, a2) in src:
        z0, tt, L1 = diff16(list(k1), a1, list(k2), a2)
        ex[z0-tt] += 1; eL1[L1] += 1; s1[len(L1)] += 1
    print(f"{label}: extra {dict(sorted(ex.items()))} | L1 sizes {dict(sorted(s1.items()))} | distinct {len(eL1)} | menu {dict(sorted(Counter(eL1.values()).items()))}")

# ---------- PART 4: in-pipeline adversarial checks ----------
# (a) fold-definition cross-check on 200 sampled cross differences
random.seed(7); mism = 0
for _ in range(200):
    wk, wa = WIT[random.randrange(35)]; dk, da = DEN[random.randrange(1344)]
    d = [(a-b) % P for a, b in zip(wk, dk)]
    vals = [peval(d, x) for x in H32]
    L1a = frozenset(i for i in range(16) if vals[i] == 0 and vals[i+16] == 0)
    L1b = frozenset(i for i in range(16)
                    if (vals[i] + vals[i+16]) % P == 0
                    and (vals[i]*H32[i] + vals[i+16]*H32[i+16]) % P == 0)
    if L1a != L1b: mism += 1
print(f"\nAUDIT (a) fold-def vs point-fiber, 200 pairs: {mism} mismatches")
# (b) negation-pair differences are even (single depth-1 class)
def neg_poly(c): return tuple((co if j % 2 == 0 else (P-co) % P) for j, co in enumerate(c))
DSET = {k: i for i, (k, _) in enumerate(DEN)}
negsp = Counter(); seen = 0
for k, _ in DEN:
    nk = neg_poly(k)
    if nk in DSET and k < nk:
        d = [(a-b) % P for a, b in zip(k, nk)]
        negsp[tuple(spread_of(d, dd) for dd in (1, 2, 3))] += 1
        seen += 1
print(f"AUDIT (b) negation pairs found {seen}; difference spreads {dict(negsp.most_common(3))}")
