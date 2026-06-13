#!/usr/bin/env python3
"""r=5 stratum at s=32: structural chart in canonical (phi-frame) coordinates.

Canonical reduction (proven in DERIVED-99512.md):
  parity-pure O (Lemma P below, proven for all 2-power s), o_i = 2u_i + pi,
  pi in {0,1}; sign lifts a_i = o_i + 32 m_i; psi_i = (a_i - pi)/2 = u_i + 16 s_i,
  s_i = m_i.  The 16 non-B balance terms (phi-fibers in Z_32, axis = fiber mod 16,
  side = fiber div 16):
    doubles  D_i : axis 2u_i mod 16,        side rho_i = [u_i >= 8]   (s-independent)
    products P_ij: axis (u_i+u_j) mod 16,   side gamma_ij ^ s_i ^ s_j,
                   gamma_ij = [u_i+u_j >= 16]  (reps in [0,16))
    Lambda   L   : axis lam = 8 - pi,       side 1                    (fixed)
  O-fiber of i sits at axis 2u_i mod 16, side rho_i (same slot as D_i).
  B placement law: per axis d = (#side0 - #side1); feasible iff |d|<=1 all axes,
  light-side fiber not an O-fiber; h = #forced, k = (14-h)/2, v = #free axes
  (d=0, no O-fiber); ways = C(v,k).

This file ENUMERATES the canonical space (2 x C(16,5) x 16 sign classes) and
charts the event taxonomy; it is gated per-class against the independent
audit DP enumerator (rec32r5.txt).
"""
from itertools import combinations
from math import comb
from collections import Counter, defaultdict
import sys

M = 16            # axes
S = 2 * M         # fibers (=32)
R = 5
B = (S + 1 - R) // 2   # 14
PAIRS = list(combinations(range(R), 2))

# ---------- canonical engine ----------
def run():
    classes = []           # per feasible class: dict of all charted data
    for pi in (0, 1):
        lam = (M // 2 - pi) % M
        for U in combinations(range(M), R):
            dax = [(2 * u) % M for u in U]
            rho = [1 if u >= M // 2 else 0 for u in U]
            pax = [ (U[i] + U[j]) % M for (i, j) in PAIRS ]
            gam = [ 1 if U[i] + U[j] >= M else 0 for (i, j) in PAIRS ]
            ofib = [ dax[i] + 16 * rho[i] for i in range(R) ]   # phi-fibers of O
            oset = set(ofib)
            oaxset = set(dax)
            for sm in range(16):                  # s_1 = 0 (mod global flip)
                sb = [0] + [(sm >> (i - 1)) & 1 for i in range(1, R)]
                # term list: (axis, side, tag, id)
                terms = []
                for i in range(R):
                    terms.append((dax[i], rho[i], 'D', i))
                for t, (i, j) in enumerate(PAIRS):
                    terms.append((pax[t], gam[t] ^ sb[i] ^ sb[j], 'P', (i, j)))
                terms.append((lam, 1, 'L', None))
                # per-axis tallies
                ax = defaultdict(list)
                for (c, sd, tag, idx) in terms:
                    ax[c].append((sd, tag, idx))
                ok = True
                h = 0; forced = []; free = []
                for c in range(M):
                    tl = ax.get(c, [])
                    d = sum(1 for (sd, _, _) in tl if sd == 0) - \
                        sum(1 for (sd, _, _) in tl if sd == 1)
                    if abs(d) > 1: ok = False; break
                    if d == 1:
                        f = c + M          # forced B on side 1
                        if f in oset: ok = False; break
                        forced.append(f); h += 1
                    elif d == -1:
                        f = c
                        if f in oset: ok = False; break
                        forced.append(f); h += 1
                    else:
                        if c not in oaxset:
                            free.append(c)
                if not ok: continue
                k2 = B - h
                if k2 < 0 or k2 % 2: continue
                k = k2 // 2
                v = len(free)
                if k > v: continue
                ways = comb(v, k)
                # ---------- event taxonomy ----------
                # axis-local signatures for every multiply-occupied axis
                ev = []          # list of (axistype, on_lambda)
                e5 = 0
                lamtype = None
                for c, tl in ax.items():
                    if len(tl) < 2 and c != lam: continue
                    tags = ''.join(sorted(t for (_, t, _) in tl))
                    # count antipodal PP on this axis
                    ps = [sd for (sd, t, _) in tl if t == 'P']
                    if len(ps) == 2 and ps[0] != ps[1]: e5 += 1
                    bal = 'b' if sum(1 for (sd,_,_) in tl if sd==0) == \
                                 sum(1 for (sd,_,_) in tl if sd==1) else \
                          ('f0' if sum(1 for (sd,_,_) in tl if sd==0) > \
                                   sum(1 for (sd,_,_) in tl if sd==1) else 'f1')
                    # f0: heavy side0 -> forced B side1 ; f1: heavy side1 -> forced B side0
                    if c == lam:
                        # refined lo|hi signature (D renamed O)
                        l0 = ''.join(sorted('O' if t=='D' else t for (sd,t,_) in tl if sd==0))
                        l1 = ''.join(sorted('O' if t=='D' else t for (sd,t,_) in tl if sd==1))
                        lamtype = l0 + '|' + l1
                    else:
                        ev.append(tags + ':' + bal)
                ev.sort()
                node = (pi, lamtype, tuple(ev))
                # strata label (raw fibers 8=lo, 24=hi), per-solution split:
                # lambda-axis raw = axis 8;  phi side0 fiber lam -> raw fiber 8+? :
                # raw fiber = phi fiber + pi ; lo fiber 8 = phi lam side0, hi 24 = side1
                lo = []; hi = []
                for (sd, tag, idx) in ax.get(lam, []):
                    (hi if sd else lo).append(tag)
                for f in forced:
                    if f % M == lam:
                        (hi if f >= M else lo).append('B')
                lam_free = lam in free
                classes.append(dict(pi=pi, U=U, sm=sm, h=h, v=v, k=k, ways=ways,
                                    forced=tuple(sorted(forced)), free=tuple(free),
                                    node=node, e5=e5, lo=tuple(sorted(lo)),
                                    hi=tuple(sorted(hi)), lam_free=lam_free))
    return classes

CL = run()
print(f"feasible (O,mask) classes: {len(CL)}")
W = sum(c['ways'] for c in CL)
print(f"waysum (B,O,mask) classes: {W}")

# ---------- GATES vs audit ----------
# G1/G2
assert len(CL) == 11808, len(CL)
assert W == 99512, W

# G3 eps split (by parity pi)
wpi = Counter(); cpi = Counter()
for c in CL:
    wpi[c['pi']] += c['ways']; cpi[c['pi']] += 1
print("ways by pi (0=even O,1=odd O):", dict(wpi), " classes by pi:", dict(cpi))

# G4 E5 census
e5c = Counter(c['e5'] for c in CL)
print("E5 census over (O,mask) classes:", dict(sorted(e5c.items())))

# G5 strata table: per solution; lambda-free classes split C(v-1,k-1)/C(v-1,k)
strat = Counter()
def label(lo, hi):
    ren = {'D': 'O', 'P': 'P', 'L': 'L', 'B': 'B'}
    a = ''.join(sorted(ren[t] for t in lo)); b = ''.join(sorted(ren[t] for t in hi))
    return '|'.join(sorted([a, b]))
for c in CL:
    lo, hi, v, k = list(c['lo']), list(c['hi']), c['v'], c['k']
    if c['lam_free'] and k >= 1:
        strat[label(lo, hi + ['B'] if False else hi)] += comb(v-1, k)   # no pair on lam
        strat[label(lo + ['B'], hi + ['B'])] += comb(v-1, k-1)          # pair on lam
    else:
        strat[label(lo, hi)] += c['ways']
print("z*-axis strata (B,O,mask classes):")
for kk, vv in strat.most_common(): print(f"   {kk:8s} {vv}")

TARGET = {'L|P':23024,'BL|BP':22720,'B|L':14208,'BL|OP':12032,'BL|PP':10896,
          'L|O':7264,'BP|LO':4480,'BP|LP':2496,'LO|OP':1600,'LO|PP':504,'LP|OP':288}
ok = dict(strat) == TARGET
print("strata table matches FORECAST_n64 target:", ok)

# G6 per-class equality with audit DP records
import re
recs = {}
for line in open('/tmp/r5tax/rec32r5.txt'):
    if not line.startswith('REC'): continue
    m = re.match(r'REC (\d+) (\d+) (\d+) (\d+) (\d+) \| (\d+) \| h (\d+) :((?: \d+)*) \| v (\d+) :((?: \d+)*) \| w (\d+)', line)
    O = tuple(int(x) for x in m.group(1,2,3,4,5)); msk = int(m.group(6))
    h, v, w = int(m.group(7)), int(m.group(9)), int(m.group(11))
    fr = tuple(sorted(int(x) for x in m.group(8).split()))
    fx = tuple(sorted(int(x) for x in m.group(10).split()))
    recs[(O, msk)] = (h, v, w, fr, fx)
assert len(recs) == 11808
mism = 0
for c in CL:
    pi, U, sm = c['pi'], c['U'], c['sm']
    O = tuple(sorted((2*u + pi) % S for u in U))
    # U sorted ascending -> o = 2u+pi ascending, same order; mask bits = s_i
    key = (O, sm)
    if key not in recs: mism += 1; print("MISSING", key); continue
    h, v, w, fr, fx = recs[key]
    # my forced fibers are phi-frame: raw = (phi + pi) mod 32 ; free axes raw = (c+pi)%16
    myfr = tuple(sorted((f + pi) % S for f in c['forced']))
    myfx = tuple(sorted((a + pi) % M for a in c['free']))
    if (h, v, w) != (c['h'], c['v'], c['ways']) or fr != myfr or fx != tuple(sorted(myfx)):
        mism += 1
        if mism < 5: print("MISMATCH", key, (h,v,w,fr,fx), (c['h'],c['v'],c['ways'],myfr,myfx))
print("per-class mismatches vs audit DP:", mism)
assert mism == 0

# G7 B-multiplicity and sigma-uniqueness (expand all solutions)
BO = defaultdict(set); Bcnt = Counter()
for c in CL:
    pi, U = c['pi'], c['U']
    O = tuple(sorted((2*u + pi) % S for u in U))
    base = [ (f + pi) % S for f in c['forced'] ]
    for pick in combinations(c['free'], c['k']):
        Bf = frozenset(base) | {(a + pi) % S for a in pick} | {(a + M + pi) % S for a in pick}
        BO[(Bf, O)].add(c['sm']); Bcnt[Bf] += 1
print("masks per (B,O):", dict(Counter(len(x) for x in BO.values())))
print("B multiplicity menu:", dict(Counter(Bcnt.values())), " distinct B:", len(Bcnt))

# ---------- the node table ----------
print("\n(h,v,k) histogram over classes:", dict(sorted(Counter((c['h'],c['v'],c['k']) for c in CL).items())))
nodes = defaultdict(lambda: [0, 0, Counter()])
for c in CL:
    n = nodes[c['node']]
    n[0] += 1; n[1] += c['ways']; n[2][(c['h'], c['v'], c['k'])] += 1
print(f"\nNODE TABLE ({len(nodes)} nodes): (pi, lambda-axis type, off-lambda events) classes ways (h,v,k)")
tot_c = tot_w = 0
for key in sorted(nodes, key=lambda x: -nodes[x][1]):
    cnt, w, hvk = nodes[key]
    tot_c += cnt; tot_w += w
    print(f"  pi={key[0]} lam={str(key[1]):10s} off={str(key[2]):46s} {cnt:6d} {w:7d} {dict(hvk)}")
print(f"  CROSSFOOT: classes {tot_c}  ways {tot_w}")

# per-U sign-class multiplicity (sigma): how many sm survive per (pi,U)
sigU = Counter()
for c in CL: sigU[(c['pi'], tuple(c['U']))] += 1
print("\nfeasible (pi,U) sets:", len(sigU), " sigma histogram:", dict(Counter(sigU.values())))
print("U-geometries: distinct U per pi:", dict(Counter(p for (p, _) in sigU)))

# dump for deriv.py
import json
with open('/tmp/r5tax/classes.json', 'w') as f:
    json.dump([dict(pi=c['pi'], U=list(c['U']), sm=c['sm'], h=c['h'], v=c['v'],
                    k=c['k'], ways=c['ways'], node=[c['node'][0], c['node'][1],
                    list(c['node'][2])], e5=c['e5']) for c in CL], f)
print("dumped classes.json")
