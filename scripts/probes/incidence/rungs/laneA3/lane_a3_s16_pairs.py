#!/usr/bin/env python3
"""LANE A3 (rigidity across the lambda family) — s=16 leg (n=32), kernel-swept.

Per-lambda input: raw rows from the production census kernel compiled with
  gcc -O3 -march=native -DA=17 -DLAM=<lam>ULL census_kernel.c
(#ifndef guards verified in scripts/probes/n32census/census_kernel.c lines 18/26/33),
one full C(32,17) functional sweep per lambda — BOTH layers (agree 18 witnesses +
agree 17 marginal), the same pipeline whose canonical-lambda output distilled to the
proven 35 + 1,344 (RESULTS-INCIDENCE gates).

Per lambda this post-pass:
  1. dedupes rows (eval vectors on mu_32), IDFT -> coefficients, asserts deg < 16;
  2. splits layers by exact agreement (17 / 18; >18 impossible for deg<16 vs deg-18 e);
  3. verifies the witness layer BIT-EXACTLY equals the constructed {u_S(X^2) :
     S in e1-fiber of -lam} (the O130 anatomy, generalized off the canonical fiber);
  4. records the NEW census data: per-layer list sizes + marginal T-shape census
     (#antipodal pairs, #odd points);
  5. zero-excess check |Z0(c-c')| vs |T cap T'| via eval-vector coordinate matching:
     ALL pairs if C(L,2) <= CAP, else exhaustive W-W and W-D plus a seeded
     deterministic D-D sample filling the cap; every excess pair fully identified
     (extra indices, negation-pair status, q-root antipode mechanism check).

Usage: python3 lane_a3_s16_pairs.py <lam>:<rowdir-glob> [...]
Conventions: O129 (P=2013265921, g0=31, h=g0^((P-1)/32), z*=h^8; canonical
lam = 284861408 is the fiber-35 word; this lane sweeps fibers 10/3/1/0).
"""
import sys, glob, random
from itertools import combinations
from collections import Counter

P = 2013265921; G0 = 31
N, KDEG, S = 32, 16, 16
CAP = 100_000
SEED = 20260611

h = pow(G0, (P-1)//N, P)
H = [pow(h, i, P) for i in range(N)]
G16 = [pow(h*h % P, i, P) for i in range(N//2)]
HINV = [pow(x, P-2, P) for x in H]
invN = pow(N, P-2, P)

# e1 fiber census over 9-subsets of mu_16 (witness-layer prediction)
fib = {}
for sub in combinations(G16, 9):
    fib.setdefault(sum(sub) % P, []).append(sub)
fsz = Counter(len(v) for v in fib.values())
print(f"e1 census, 9-subsets of mu_16: {len(fib)} distinct values, "
      f"fiber-size histogram {dict(sorted(fsz.items()))}")
maxv = sorted(v for v, ss in fib.items() if len(ss) == 35)
print(f"fiber-35 values == mu_16? {maxv == sorted(G16)}\n")

def idft(vals):
    return tuple(sum(vals[i]*pow(HINV[i], d, P) for i in range(N)) % P * invN % P
                 for d in range(N))

def process(lam, pat):
    w = [(pow(x, S+2, P) + lam*pow(x, S, P)) % P for x in H]
    raw = 0; rows = set()
    for f in sorted(glob.glob(pat)):
        for line in open(f):
            raw += 1
            rows.add(tuple(map(int, line.split())))
    wit, den = [], []
    for vals in rows:
        cs = idft(list(vals))
        assert all(c == 0 for c in cs[KDEG:]), "deg >= 16 candidate"
        ag = frozenset(i for i in range(N) if vals[i] == w[i])
        assert len(ag) in (S+1, S+2), f"agreement {len(ag)}"
        (wit if len(ag) == S+2 else den).append((vals, ag))
    wit.sort(); den.sort()
    print(f"== lam={lam} (e1=-lam fiber {len(fib.get((P-lam) % P, []))}) ==")
    print(f"raw rows {raw}, distinct {len(rows)}; "
          f"LIST = {len(wit)+len(den)} = {len(wit)} witnesses (agree 18) "
          f"+ {len(den)} marginal (agree 17); "
          f"row accounting raw == 18*W+D: {raw == 18*len(wit)+len(den)}")
    # 3. constructed witness layer, bit-exact
    constructed = set()
    for Ssub in fib.get((P - lam) % P, []):
        ev = []
        for ix, x in enumerate(H):
            e = 1; x2 = x*x % P
            for z in Ssub: e = e * ((x2 - z) % P) % P
            ev.append((w[ix] - e) % P)
        constructed.add(tuple(ev))
    bitexact = constructed == {v for v, _ in wit}
    print(f"witness layer == constructed u_S(X^2) over the fiber (bit-exact): {bitexact}")
    assert bitexact
    # 4. marginal T-shape census
    shapes = Counter()
    for _, ag in den:
        pairs = sum(1 for i in range(N//2) if i in ag and i+N//2 in ag)
        shapes[(pairs, len(ag)-2*pairs)] += 1
    print(f"marginal T-shape census (antipodal pairs, odd points): "
          f"{dict(shapes.most_common())}")
    # 5. pairwise exactness
    items = wit + den
    L = len(items); total = L*(L-1)//2
    def excess(p1, p2):
        (v1, a1), (v2, a2) = p1, p2
        z0 = sum(1 for i in range(N) if v1[i] == v2[i])
        return z0 - len(a1 & a2)
    ex = {"W-W": Counter(), "W-D": Counter(), "D-D": Counter()}
    bad = []
    def note(lay, p1, p2, tag):
        e = excess(p1, p2)
        ex[lay][e] += 1
        if e:
            (v1, a1), (v2, a2) = p1, p2
            extras = [i for i in range(N) if v1[i] == v2[i]
                      and not (i in a1 and i in a2)]
            isneg = v2 == tuple(v1[(i+N//2) % N] for i in range(N))
            # q-root antipode mechanism: every extra zero's antipode in T cap T'?
            mech = all((i+N//2) % N in (a1 & a2) for i in extras)
            bad.append((lay, tag, e, extras, isneg, mech))
    nW = len(wit)
    for i, j in combinations(range(nW), 2): note("W-W", items[i], items[j], (i, j))
    for i in range(nW):
        for j in range(nW, L): note("W-D", items[i], items[j], (i, j))
    done = sum(sum(c.values()) for c in ex.values())
    dd_total = len(den)*(len(den)-1)//2
    if total <= CAP:
        for i, j in combinations(range(len(den)), 2):
            note("D-D", den[i], den[j], (nW+i, nW+j))
        dd_mode = f"ALL {dd_total}"
    else:
        budget = CAP - done
        random.seed(SEED)
        idx = set()
        while len(idx) < budget:
            i, j = random.randrange(len(den)), random.randrange(len(den))
            if i < j: idx.add((i, j))
        for i, j in sorted(idx): note("D-D", den[i], den[j], (nW+i, nW+j))
        dd_mode = f"seeded sample {budget}/{dd_total} (seed {SEED})"
    print(f"pairs checked: W-W all {nW*(nW-1)//2}, W-D all {nW*len(den)}, D-D {dd_mode}")
    print("excess histograms: "
          + "; ".join(f"{k} {dict(sorted(v.items()))}" for k, v in ex.items() if v))
    for lay, tag, e, extras, isneg, mech in bad:
        print(f"  EXCESS [{lay}] pair {tag}: +{e} extra idx {extras} "
              f"negation={isneg} antipode-mechanism={mech}")
    print()
    return (lam, len(fib.get((P-lam) % P, [])), len(wit), len(den),
            {k: dict(sorted(v.items())) for k, v in ex.items() if v}, len(bad))

results = [process(int(a.split(":")[0]), a.split(":", 1)[1]) for a in sys.argv[1:]]
print("==== SUMMARY (s=16) ====")
print(f"{'lam':>11s} {'fiber':>5s} {'wit':>4s} {'marg':>6s}  excess>0 pairs")
for lam, fb, nw, nd, exh, nbad in results:
    print(f"{lam:11d} {fb:5d} {nw:4d} {nd:6d}  {nbad}   {exh}")
