#!/usr/bin/env python3
"""The DERIVATION engine for the r=5 stratum at s=32.

Counts the stratum with NO enumeration of sign-vectors and NO placement DP:
  per (pi, U) geometry:
    - place the 16 terms on axes (doubles/Lambda fixed sides, product sides
      symbolic affine functionals of s in GF(2)^4 = GF(2)^5 / <global flip>),
    - per multi-term axis enumerate the ADMISSIBLE side-patterns
      (|d| <= 1, forced light fiber not an O-fiber)   [event taxonomy],
    - per combination of patterns: sigma = 2^(4 - rank) by Gaussian
      elimination if consistent (else 0)              [sigma law],
    - h = # |d|=1 axes, v = # d=0 axes with no O-fiber, k = (14-h)/2,
      ways = C(v,k) * sigma                           [placement law].
Gated per-(pi,U) and per-node against the chart enumeration (classes.json),
which itself is gated per-class against the independent audit DP.
"""
from itertools import combinations, product
from math import comb
from collections import Counter, defaultdict
import json

M, S, R, B = 16, 32, 5, 14
PAIRS = list(combinations(range(R), 2))

def solve_rank(eqs):
    """eqs: list of (mask4, const). Return rank or None if inconsistent."""
    rows = list(eqs); basis = {}
    for m, c in rows:
        while m:
            p = m.bit_length() - 1
            if p in basis:
                bm, bc = basis[p]; m ^= bm; c ^= bc
            else:
                basis[p] = (m, c); break
        else:
            if c: return None
    return len(basis)

def run(Mloc=16, dump_nodes=True):
    nodes = defaultdict(lambda: [0, 0])     # sig -> [classes, ways]
    perU = {}
    tot_c = tot_w = 0
    for pi in (0, 1):
        lam = (Mloc // 2 - pi) % Mloc
        for U in combinations(range(Mloc), R):
            ax = defaultdict(list)   # axis -> list of terms
            oax = {}                 # axis -> set of O sides
            for i, u in enumerate(U):
                a = (2 * u) % Mloc; rho = 1 if u >= Mloc // 2 else 0
                ax[a].append(('D', rho, 0, 0))      # tag, fixed side, mask, isP
                oax.setdefault(a, set()).add(rho)
            for t, (i, j) in enumerate(PAIRS):
                a = (U[i] + U[j]) % Mloc
                gam = 1 if U[i] + U[j] >= Mloc else 0
                msk = ((1 << (i - 1)) if i else 0) ^ (1 << (j - 1))
                ax[a].append(('P', gam, msk, 1))
            ax[lam].append(('L', 1, 0, 0))
            # classify axes
            single_h = 0
            empty = Mloc - len(ax)
            cons = []   # per constraint-axis: list of admissible (eqs,d,free,sig,c)
            okU = True
            for c, tl in ax.items():
                if len(tl) == 1:
                    single_h += 1     # lone term: |d|=1, light side never in O
                    continue
                prods = [t for t in tl if t[3]]
                fixed = [t for t in tl if not t[3]]
                f0 = sum(1 for t in fixed if t[1] == 0)
                f1 = sum(1 for t in fixed if t[1] == 1)
                osides = oax.get(c, set())
                adm = []
                for bits in product((0, 1), repeat=len(prods)):
                    d = f0 - f1 + sum(1 if b == 0 else -1 for b in bits)
                    if abs(d) > 1: continue
                    if d == 1 and 1 in osides: continue   # B side1 blocked by O
                    if d == -1 and 0 in osides: continue  # B side0 blocked by O
                    eqs = [(p[2], p[1] ^ b) for p, b in zip(prods, bits)]
                    # gamma ^ (s_i^s_j) = side b  =>  s_i^s_j = gamma ^ b
                    freeax = (d == 0 and not osides)
                    # signature
                    sides = [(t[0], t[1]) for t in fixed] + \
                            [('P', b) for b in bits]
                    if c == lam:
                        l0 = ''.join(sorted('O' if t=='D' else t for (t,sd) in sides if sd==0))
                        l1 = ''.join(sorted('O' if t=='D' else t for (t,sd) in sides if sd==1))
                        sig = l0 + '|' + l1
                    else:
                        tags = ''.join(sorted(t for (t, _) in sides))
                        bal = 'b' if d == 0 else ('f0' if d > 0 else 'f1')
                        sig = tags + ':' + bal
                    adm.append((eqs, d, freeax, sig, c == lam))
                if not adm: okU = False; break
                cons.append(adm)
            if not okU: continue
            lam_single = len(ax[lam]) == 1
            ucl = uw = 0
            for combo in product(*cons) if cons else [()]:
                eqs = [e for pat in combo for e in pat[0]]
                rk = solve_rank(eqs)
                if rk is None: continue
                sigma = 1 << (4 - rk)
                h = single_h + sum(1 for pat in combo if pat[1] != 0)
                v = empty + sum(1 for pat in combo if pat[2])
                if (B - h) < 0 or (B - h) % 2: continue
                k = (B - h) // 2
                if k > v: continue
                w = comb(v, k)
                lamsig = '|L' if lam_single else \
                         next(p[3] for p in combo if p[4])
                off = tuple(sorted(p[3] for p in combo if not p[4]))
                nodes[(pi, lamsig, off)][0] += sigma
                nodes[(pi, lamsig, off)][1] += sigma * w
                ucl += sigma; uw += sigma * w
            if ucl:
                perU[(pi, U)] = (ucl, uw)
                tot_c += ucl; tot_w += uw
    return nodes, perU, tot_c, tot_w

nodes, perU, tot_c, tot_w = run()
print(f"DERIVED: classes {tot_c}  ways {tot_w}")
assert (tot_c, tot_w) == (11808, 99512), (tot_c, tot_w)

# ---- gate against chart enumeration, per (pi,U) and per node ----
CL = json.load(open('/tmp/r5tax/classes.json'))
chart_perU = Counter(); chart_nodes = defaultdict(lambda: [0, 0])
for c in CL:
    chart_perU[(c['pi'], tuple(c['U']))] += 1
    key = (c['pi'], c['node'][1], tuple(c['node'][2]))
    chart_nodes[key][0] += 1; chart_nodes[key][1] += c['ways']
bad = 0
for kk, (ucl, uw) in perU.items():
    if chart_perU.get(kk, 0) != ucl: bad += 1
for kk in chart_perU:
    if kk not in perU: bad += 1
print("per-(pi,U) sigma mismatches:", bad)
nb = 0
for kk in set(nodes) | set(chart_nodes):
    if list(nodes.get(kk, [0, 0])) != list(chart_nodes.get(kk, [0, 0])):
        nb += 1; print("NODE MISMATCH", kk, nodes.get(kk), chart_nodes.get(kk))
print("node mismatches:", nb)
assert bad == 0 and nb == 0

# ---- emit the full node table ----
with open('/tmp/r5tax/NODE-TABLE.txt', 'w') as f:
    f.write("# r=5 s=32 node table, derived by sigma-rank engine (deriv.py)\n")
    f.write("# pi  lambda-axis  off-lambda-events  classes  ways\n")
    for kk in sorted(nodes, key=lambda x: (-nodes[x][1], str(x))):
        cnt, w = nodes[kk]
        f.write(f"pi={kk[0]} lam={kk[1]:8s} off={','.join(kk[2]) or '-':50s} {cnt:6d} {w:7d}\n")
    f.write(f"# CROSSFOOT classes {tot_c} ways {tot_w}\n")
print("wrote NODE-TABLE.txt")

# ---- aggregated views for the doc ----
print("\nlambda-marginal (classes, ways) by (pi, lamsig):")
lm = defaultdict(lambda: [0, 0])
for (pi, lamsig, off), (cnt, w) in nodes.items():
    lm[(pi, lamsig)][0] += cnt; lm[(pi, lamsig)][1] += w
for kk in sorted(lm, key=lambda x: (x[0], -lm[x][1])):
    print(f"   pi={kk[0]} lam={kk[1]:8s} classes {lm[kk][0]:6d} ways {lm[kk][1]:7d}")

print("\noff-lambda event-multiset marginal (top):")
om = defaultdict(lambda: [0, 0])
for (pi, lamsig, off), (cnt, w) in nodes.items():
    om[off][0] += cnt; om[off][1] += w
for kk in sorted(om, key=lambda x: -om[x][1])[:20]:
    print(f"   {','.join(kk) or '-':52s} classes {om[kk][0]:6d} ways {om[kk][1]:7d}")
