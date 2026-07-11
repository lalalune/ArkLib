"""u-triple censuses per taxonomy node as functions of m = s/2 (r=3 stratum).
For each s in {8,16,32}: group feasible (O,sigma) classes by (eps,label),
report (#u-triples, sigma-mult); check the universal node-geometry law:
  k = (m-1-h)/2  and  v = m + c_node  with s-independent (h, c_node).
Also: dead-triple census at eps=0, and closed-form checks (E1 = M(m-2), etc).
"""
import sys
sys.path.insert(0, '/tmp/genlaw')
from engine import run, label
from collections import defaultdict, Counter
from itertools import combinations
from math import comb

GEOM = {}   # label-pattern -> (h, voffset) ; check s-independence

for s in (8, 16, 32):
    m = s // 2
    M = m // 2
    R = run(s, collect_elements=False)
    by = defaultdict(list)
    for r in R['recs']:
        lab = label(s, r['O'], r['sig'])
        # normalize E4 fibers to symbolic {lo,hi}
        e4 = tuple('lo' if o == s // 4 else 'hi' for o in lab[4])
        key = (lab[0], lab[1], lab[2], lab[3], e4)
        by[key].append(r)
    print(f"== s={s} (m={m}) per-node: (#u, sigma-mult, h, v, k) ==")
    live_u = {0: set(), 1: set()}
    for key in sorted(by, key=str):
        rs = by[key]
        us = defaultdict(set)
        for r in rs:
            eps = r['O'][0] % 2
            u = tuple(sorted((o - eps) // 2 for o in r['O']))
            us[u].add(r['sig'])
            live_u[eps].add((eps, u))
        sigmults = {len(v) for v in us.values()}
        hs = {r['h'] for r in rs}
        vs = {r['v'] for r in rs}
        ks = {r['k'] for r in rs}
        assert len(sigmults) == 1 and len(hs) == 1 and len(vs) == 1
        h, v, k = hs.pop(), vs.pop(), ks.pop()
        assert k == (m - 1 - h) // 2, (key, h, k)
        geokey = key[1:]  # drop eps for geometry (eps only via E4 availability)
        voff = v - m
        gk = (key[1], key[2], key[3], key[4], key[0])  # include eps: E3 free-bonus?
        if gk in GEOM:
            assert GEOM[gk] == (h, voff), (gk, GEOM[gk], (h, voff))
        else:
            GEOM[gk] = (h, voff)
        nu = len(us)
        sg = sigmults.pop()
        print(f"  {str(key):46s} #u={nu:3d} sig={sg} h={h} v=m{voff:+d}={v:2d} "
              f"k={k}  cls={nu*sg:4d} ways={comb(v,k):4d} sub={nu*sg*comb(v,k):6d}")
    # dead census at each eps
    for eps in (0, 1):
        tot = comb(m, 3)
        live = len(live_u[eps])
        print(f"  eps={eps}: live u-triples {live} / {tot}  (dead {tot - live})")
    # closed-form checks
    e1tot = {0: 0, 1: 0}
    for eps in (0, 1):
        for T in combinations(range(m), 3):
            if any((b - a) % m == M for a, b in combinations(T, 2)):
                e1tot[eps] += 1
    print(f"  E1 u-census per eps (all, incl. dead): {e1tot}  formula M(m-2) = {M*(m-2)}")
    print()

print("Universal node geometry (label -> (h, v-m)), s-independent across 8/16/32:")
for gk in sorted(GEOM, key=str):
    print(f"  {str(gk):52s} h={GEOM[gk][0]}  v=m{GEOM[gk][1]:+d}")
