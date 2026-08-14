#!/usr/bin/env python3
"""LANE G2+G3 at n=64 (s=32), BabyBear -- redesigned for O134.

Pre-registered: scripts/probes/incidence/rungs/HYPOTHESES.md (G2 exactness at rung 3,
G3 dichotomy generality; menu blind test = G1's general-s law).
Conventions: O129 (scripts/probes/incidence/RESULTS-INCIDENCE.md) + O130/O134
(scripts/probes/genlaw/construct_n64.py, scripts/probes/genlaw/falsifier/RESULTS.md):
  P = 15*2^27+1 (BabyBear), g0 = 31, h = g0^((P-1)/64), H = mu_64 = powers of h,
  G[z] = H[2z] (squares domain mu_32, indices 0..31), z* = H[16] = G[8],
  lam = P - z* (canonical, = 284861408), word w = X^34 + lam*X^32.
Witness layer (agree 34): c_w = w - E(X^2), E = (Y - z*) * prod_{z in I} (Y^2 - G[z]^2),
  I an 8-subset of the 15 non-z* antipodal axes of mu_32 -> C(15,8) = 6435 witnesses,
  even, deg <= 30, S = {8} u {z, z+16 : z in I} (G-index sets).
Marginal layer r=3 (agree 33): e = prod_{b in B}(X^2 - G[b]) (X-x1)(X-x2)(X-x3)(X-xi),
  xi = -(x1+x2+x3), B a 15-subset of G-indices {0..31} \ O, x_i = H[O_i + 32*d_i];
  consistency: e2(x) - e1(x)^2 = lam + e1(B_z)  <=>  coeff(X^32) of e = lam.
O134 input: the 11 BabyBear r=3 spurious (B,O,sigma) solutions (char-0-INFEASIBLE
classes, genuine mod-p marginal codewords, agree exactly 33), verbatim from
scripts/probes/genlaw/falsifier/brute_bb_r3.txt.

Tests on all 6435 witnesses x (census sample + spurious) marginal elements:
  G2 exactness:  |Z0(c_w - c_t)| == |T_w cap T_t| per pair.
  G3 dichotomy:  L1 dead fibers (both antipodal branches zero) == S cap B per pair.
  MENU (G1 general law at s=32): per marginal element, locus multiplicities over the
    6435 witnesses == C(m0, 8 - |A| - |J|), where A = chosen B-FULL axes (new at
    s=32: full antipodal pairs inside B exist here, unlike the s=16 census),
    J = chosen B-half axes, m0 = #B-empty axes among the 15 non-z* axes; constant
    locus part = B cap {8}.
Exact integer arithmetic; numpy only for int64/bool equality counting (< 2^31: exact).
"""
import json, random, sys, time
from collections import Counter
from itertools import combinations
from math import comb

import numpy as np

T0 = time.time()
def tick(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)

P = 15 * (1 << 27) + 1
g0 = 31
n, s = 64, 32
h = pow(g0, (P - 1) // n, P)
H = [pow(h, i, P) for i in range(n)]
G = [H[(2 * z) % n] for z in range(s)]
ZS = pow(g0, (P - 1) // 4, P)
assert ZS == H[16] == G[8]
LAM = (P - ZS) % P
assert LAM == 284861408, f"canonical lam mismatch: {LAM}"
wev = [(pow(x, s + 2, P) + LAM * pow(x, s, P)) % P for x in H]
Hset = set(H)
AX = [z for z in range(16) if z != 8]          # the 15 non-z* antipodal axes
print(f"p = {P}, h = {h}, z* = {ZS}, lam = {LAM} (canonical), g0 = {g0}")

def horner(coeffs, x):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % P
    return acc

# ============================================================================
# 1. WITNESS LAYER: all C(15,8) = 6435 elements, each verified individually
# ============================================================================
wit_I = list(combinations(AX, 8))
NW = len(wit_I)
assert NW == comb(15, 8) == 6435
CW  = np.empty((NW, 64), np.int64)   # witness evaluation vectors on H
TWb = np.zeros((NW, 64), bool)       # agreement sets T_w (positions in H)
SAX = np.zeros((NW, 32), bool)       # S as G-index sets
for wi, I in enumerate(wit_I):
    E = [LAM, 1]                                       # (Y - z*)
    for z in I:                                        # * (Y^2 - G[z]^2)
        c2 = (G[z] * G[z]) % P
        nE = [0] * (len(E) + 2)
        for t, co in enumerate(E):
            nE[t + 2] = (nE[t + 2] + co) % P
            nE[t] = (nE[t] - co * c2) % P
        E = nE
    # monic deg 17 in Y, coeff(Y^16) = lam  =>  u = Y^17+lam Y^16-E has deg_Y <= 15
    # =>  c_w = w - E(X^2) is EVEN with deg <= 30 (codeword), structurally.
    assert len(E) == 18 and E[17] == 1 and E[16] == LAM
    S = {8} | set(I) | {z + 16 for z in I}
    Eg = [horner(E, G[j]) for j in range(32)]
    zr = {j for j in range(32) if Eg[j] == 0}
    assert zr == S and len(S) == 17, "witness agreement set wrong"
    for i in range(64):
        CW[wi, i] = (wev[i] - Eg[i % 32]) % P
    for j in S:
        TWb[wi, j] = TWb[wi, j + 32] = True
        SAX[wi, j] = True
assert (TWb.sum(1) == 34).all()                        # agree exactly 34
assert (CW[:, :32] == CW[:, 32:]).all()                # even as functions on H
assert len(np.unique(CW, axis=0)) == NW                # 6435 distinct codewords
tick(f"witness layer: {NW} = C(15,8) elements built; each verified: even, "
     f"deg<=30 (E[16]=lam,E[17]=1), agreement EXACTLY 34 = predicted S-fibers; "
     f"all distinct")

# ============================================================================
# 2. CHAR-0 PLACEMENT ENUMERATION (lattice balance in Z[zeta_2s]/(zeta^s = -1))
#    alpha = e2(x) + e1(O_z) + e1(B_z) - z* must vanish as a lattice vector.
#    Non-B part V; per axis beta: required B-contribution r_b = -V[2*beta] in
#    {-1,0,+1}; forced axes h, free axes v (both antipodes available, r=0),
#    count = C(v, (bsize-h)/2).  [the DERIVED placement rule, re-derived]
# ============================================================================
def lattice_V(sv, O, sg):
    """Non-B part of alpha for class (O, sigma), dvec = (0, sg[0], sg[1])."""
    d = (0, sg[0], sg[1])
    V = [0] * sv
    for i, j in ((0, 1), (0, 2), (1, 2)):              # e2(x) terms
        sign = -1 if (d[i] + d[j]) % 2 else 1
        t = (O[i] + O[j]) % (2 * sv)
        if t >= sv:
            t -= sv; sign = -sign
        V[t] += sign
    for Oi in O:                                       # e1(O_z) terms
        sign, t = 1, (2 * Oi) % (2 * sv)
        if t >= sv:
            t -= sv; sign = -sign
        V[t] += sign
    V[sv // 2] -= 1                                    # -z*
    return V

def b_axis_contrib(sv, B):
    """Per-axis B contribution: +1 if beta in B, -1 if beta+sv/2 in B (sum)."""
    half = sv // 2
    c = [0] * half
    for b in B:
        c[b % half] += 1 if b < half else -1
    return c

def enum_classes(sv):
    """All (O, sigma) classes at scale sv = s; returns class records."""
    half, bsize = sv // 2, sv // 2 - 1
    recs = []
    for O in combinations(range(sv), 3):
        for sg in ((0, 0), (0, 1), (1, 0), (1, 1)):
            V = lattice_V(sv, O, sg)
            if any(V[t] for t in range(1, sv, 2)):     # odd coords must vanish
                recs.append((O, sg, None, None, 0)); continue
            forced, free, ok = [], [], True
            for beta in range(half):
                r = -V[2 * beta]
                if r == 1:
                    if beta in O: ok = False; break
                    forced.append(beta)
                elif r == -1:
                    if beta + half in O: ok = False; break
                    forced.append(beta + half)
                elif r == 0:
                    if beta not in O and beta + half not in O:
                        free.append(beta)
                else:
                    ok = False; break
            if not ok:
                recs.append((O, sg, None, None, 0)); continue
            hh = len(forced)
            if (bsize - hh) % 2 or bsize - hh < 0:
                recs.append((O, sg, None, None, 0)); continue
            k = (bsize - hh) // 2
            cnt = comb(len(free), k) if k <= len(free) else 0
            recs.append((O, sg, tuple(forced), tuple(free), cnt))
    return recs

# calibration gate at n=32 (must reproduce the exhaustive O98/O129 census: 672)
recs32 = enum_classes(16)
tot32 = sum(r[4] for r in recs32)
assert len(recs32) == 2240, len(recs32)
assert tot32 == 672, f"n=32 calibration FAILED: {tot32}"
tick(f"calibration n=32: placement enumeration over 2,240 classes -> total 672 "
     f"solutions == exhaustive O98/O129 census  [GATE PASSED]")

recs64 = enum_classes(32)
tot64 = sum(r[4] for r in recs64)
feas64 = [r for r in recs64 if r[4] > 0]
assert len(recs64) == 19840, len(recs64)
assert tot64 == 764544, f"n=64 char-0 total mismatch: {tot64}"
assert len(feas64) == 3304, f"n=64 feasible classes mismatch: {len(feas64)}"
strata = Counter()
for O, sg, fo, fr, cnt in feas64:
    strata[(len(fo), len(fr), (15 - len(fo)) // 2)] += 1
tick(f"n=64 r=3 char-0 census reproduced: 19,840 classes, total 764,544 "
     f"solutions, 3,304 feasible classes  [GATES PASSED]")
print(f"  (h,v,k) strata of feasible classes: {dict(sorted(strata.items()))}")

# ============================================================================
# 3. MARGINAL ELEMENT BUILDER + FULL PER-ELEMENT VERIFICATION
# ============================================================================
def build_marginal(B, O, dvec):
    """e = prod_B (X^2-G[b]) (X-x1)(X-x2)(X-x3)(X-xi); returns evals + checks."""
    X3 = [H[(O[i] + s * dvec[i]) % n] for i in range(3)]
    xi = (-(X3[0] + X3[1] + X3[2])) % P
    A = [1]                                            # A(Y) = prod (Y - G[b])
    for b in sorted(B):
        zb = G[b]
        nA = [0] * (len(A) + 1)
        for t, c in enumerate(A):
            nA[t + 1] = (nA[t + 1] + c) % P
            nA[t] = (nA[t] - c * zb) % P
        A = nA
    e = [0] * (2 * len(A) - 1)                         # A(X^2)
    for t, c in enumerate(A):
        e[2 * t] = c
    for r in X3 + [xi]:                                # * quartic
        ne = [0] * (len(e) + 1)
        for t, c in enumerate(e):
            ne[t + 1] = (ne[t + 1] + c) % P
            ne[t] = (ne[t] - c * r) % P
        e = ne
    return e, X3, xi

def verify_element(B, O, sg, flip, tag):
    """Full verification; returns pool record or raises."""
    dvec = tuple((flip + d) % 2 for d in (0, sg[0], sg[1]))
    e, X3, xi = build_marginal(B, O, dvec)
    assert len(e) == 35 and e[34] == 1, f"{tag}: not monic deg 34"
    assert e[33] == 0, f"{tag}: coeff(X^33) != 0"
    assert e[32] == LAM, f"{tag}: consistency coeff(X^32) != lam"
    # consistency equation in field form: e2(x) - e1(x)^2 == lam + e1(B_z)
    e1x = sum(X3) % P
    e2x = (X3[0]*X3[1] + X3[0]*X3[2] + X3[1]*X3[2]) % P
    assert (e2x - e1x * e1x) % P == (LAM + sum(G[b] for b in B)) % P, \
        f"{tag}: consistency equation FAILS"
    assert xi not in Hset and xi != 0, f"{tag}: xi in mu_64 u {{0}}"
    ev = [horner(e, H[i]) for i in range(64)]
    ct = [(wev[i] - ev[i]) % P for i in range(64)]
    Tpred = sorted([b for b in B] + [b + 32 for b in B]
                   + [(O[i] + 32 * dvec[i]) % 64 for i in range(3)])
    zeros = [i for i in range(64) if ev[i] == 0]
    assert zeros == Tpred and len(zeros) == 33, \
        f"{tag}: agreement set wrong ({len(zeros)} pts)"
    # char-0 balance status: alpha as lattice vector in Z[zeta_64]/(zeta^32=-1)
    V = lattice_V(s, O, sg)
    bc = b_axis_contrib(s, B)
    Vt = list(V)
    for beta in range(16):
        Vt[2 * beta] += bc[beta]
    alpha_is_zero = not any(Vt)
    # alpha(h) must vanish mod p in all cases (== membership mod p)
    assert sum(Vt[j] * H[j] for j in range(32)) % P == 0, f"{tag}: alpha(h) != 0"
    # menu profile over the 15 non-z* axes
    F, Nmap, m0 = [], {}, 0
    for beta in AX:
        lo, hi = beta in B, beta + 16 in B
        if lo and hi: F.append(beta)
        elif lo: Nmap[beta] = beta
        elif hi: Nmap[beta] = beta + 16
        else: m0 += 1
    return dict(tag=tag, B=tuple(sorted(B)), O=tuple(O), sg=tuple(sg), flip=flip,
                ct=ct, Tpred=Tpred, F=tuple(F), Nmap=Nmap, m0=m0,
                const8=(8 in B), alpha0=alpha_is_zero)

# ---- 3a. the 11 O134 spurious solutions, verbatim from brute_bb_r3.txt --------
SPUR_RAW = [
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 9, 11, 16, 17, 19, 24, 25, 26, 27, 28)),
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 9, 13, 16, 17, 19, 24, 25, 26, 28, 29)),
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 11, 13, 16, 17, 19, 24, 26, 27, 28, 29)),
    ((5, 20, 31), 2, (2, 4, 6, 7, 9, 11, 13, 16, 19, 24, 25, 26, 27, 28, 29)),
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 9, 14, 16, 17, 19, 24, 25, 26, 28, 30)),
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 11, 14, 16, 17, 19, 24, 26, 27, 28, 30)),
    ((5, 20, 31), 2, (2, 4, 6, 7, 9, 11, 14, 16, 19, 24, 25, 26, 27, 28, 30)),
    ((5, 20, 31), 2, (1, 2, 4, 6, 7, 13, 14, 16, 17, 19, 24, 26, 28, 29, 30)),
    ((5, 20, 31), 2, (2, 4, 6, 7, 9, 13, 14, 16, 19, 24, 25, 26, 28, 29, 30)),
    ((5, 20, 31), 2, (2, 4, 6, 7, 11, 13, 14, 16, 19, 24, 26, 27, 28, 29, 30)),
    ((14, 17, 21), 1, (2, 3, 6, 7, 9, 11, 12, 13, 15, 16, 20, 22, 24, 26, 31)),
]
SIGMAS = ((0, 0), (0, 1), (1, 0), (1, 1))
pool = []
mask_map = {}
for O, m, B in SPUR_RAW:
    assert len(set(B)) == 15 and not set(B) & set(O)
    working = []
    for sg in SIGMAS:
        e, _, _ = build_marginal(B, O, (0, sg[0], sg[1]))
        if e[33] == 0 and e[32] == LAM:
            working.append(sg)
    assert len(working) == 1, f"spurious O={O} B={B}: masks {working} work"
    sg = working[0]
    mask_map.setdefault(m, set()).add(sg)
    # my placement enum must call this class char-0 infeasible (dossier: char0=0)
    rec = next(r for r in recs64 if r[0] == O and r[1] == sg)
    assert rec[4] == 0, f"spurious class (O={O},sg={sg}) is char-0 FEASIBLE?!"
    for flip in (0, 1):
        el = verify_element(B, O, sg, flip, f"spur(O={O},m={m},flip={flip})")
        assert not el['alpha0'], "spurious element is char-0 balanced?!"
        pool.append(el)
nspur = len(pool)
tick(f"O134 spurious layer reconstructed: 11 (B,O,sigma) solutions x 2 signs = "
     f"{nspur} elements; every one verified: agree EXACTLY 33, coeff(X^32)=lam, "
     f"xi outside mu_64, alpha != 0 in Z[zeta_64] (char-0 INFEASIBLE class) "
     f"with alpha(h) == 0 mod p")
print(f"  sigma-mask convention recovered: m -> sigma = "
      f"{ {m: sorted(v) for m, v in sorted(mask_map.items())} }")

# ---- 3b. census sample: >= 300 elements via weighted-uniform solution draws ---
random.seed(20260611)
classes, weights = [], []
for O, sg, fo, fr, cnt in feas64:
    classes.append((O, sg, fo, fr)); weights.append(cnt)
seen = set()
target_sols = 170
draws = 0
while len(seen) < target_sols:
    (O, sg, fo, fr) = random.choices(classes, weights=weights, k=1)[0]
    k = (15 - len(fo)) // 2
    chosen = random.sample(fr, k)
    B = tuple(sorted(list(fo) + [b for beta in chosen for b in (beta, beta + 16)]))
    key = (O, sg, B)
    draws += 1
    if key in seen:
        continue
    seen.add(key)
    for flip in (0, 1):
        el = verify_element(B, O, sg, flip, f"census(O={O},sg={sg},flip={flip})")
        assert el['alpha0'], "census element NOT char-0 balanced?!"
        pool.append(el)
ncen = len(pool) - nspur
cls_cov = len({(el['O'], el['sg']) for el in pool if el['tag'].startswith('census')})
str_cov = len({(15 - el['m0'] - len(el['F']) + (0), ) for el in pool})  # info only
tick(f"census sample: {target_sols} distinct (B,O,sigma) solutions drawn "
     f"weighted-uniform from the 764,544 (over {cls_cov} distinct classes; "
     f"{draws} draws) x 2 signs = {ncen} elements; every one verified: "
     f"agree EXACTLY 33, consistency equation holds, alpha == 0 (char-0 balanced)")

M = len(pool)
CT  = np.array([el['ct'] for el in pool], np.int64)
TTb = np.zeros((M, 64), bool)
BIX = np.zeros((M, 32), bool)
for mi, el in enumerate(pool):
    for i in el['Tpred']:
        TTb[mi, i] = True
    for b in el['B']:
        BIX[mi, b] = True
assert len(np.unique(CT, axis=0)) == M, "duplicate marginal codewords in pool"
print(f"  marginal pool: {M} distinct elements ({ncen} census + {nspur} spurious)")

# ---- 3c. negative control: 50 random non-coset (B,O,sigma) must fail ---------
fails = 0
tried = 0
while tried < 50:
    O = tuple(sorted(random.sample(range(s), 3)))
    sg = random.choice(SIGMAS)
    rest = [z for z in range(s) if z not in O]
    B = tuple(sorted(random.sample(rest, 15)))
    rec = next(r for r in recs64 if r[0] == O and r[1] == sg)
    if rec[4] > 0:  # skip true coset members (placement test)
        bc = b_axis_contrib(s, B)
        V = lattice_V(s, O, sg)
        if all(bc[beta] == -V[2 * beta] for beta in range(16)):
            continue
    tried += 1
    e, _, _ = build_marginal(B, O, (0, sg[0], sg[1]))
    if e[32] != LAM:
        fails += 1
    else:
        print(f"  !! random non-solution PASSED mod p (NEW spurious?): "
              f"B={B} O={O} sg={sg}")
assert fails == 50
tick(f"negative control: 50/50 random non-coset (B,O,sigma) FAIL coeff(X^32)=lam")

# ============================================================================
# 4. PAIR TESTS: all 6435 x M pairs -- G2 exactness, G3 dichotomy, G1 menu
# ============================================================================
bitw = (np.uint64(1) << np.arange(32, dtype=np.uint64))
g2_viol, g3_viol, g2_dump = [], [], []
menu_fail = []
z0_hist = {'census': Counter(), 'spurious': Counter()}
dead_hist = {'census': Counter(), 'spurious': Counter()}
menu_pass = {'census': 0, 'spurious': 0}
mult_menu = {'census': Counter(), 'spurious': Counter()}

for mi, el in enumerate(pool):
    grp = 'spurious' if el['tag'].startswith('spur') else 'census'
    eq = (CW == CT[mi])                                # 6435 x 64
    z0 = eq.sum(1)
    inter = (TWb & TTb[mi]).sum(1)
    bad = np.nonzero(z0 != inter)[0]
    for wi in bad:
        extra = sorted(int(x) for x in
                       set(np.nonzero(eq[wi])[0]) - set(np.nonzero(TWb[wi] & TTb[mi])[0]))
        g2_viol.append((wi, mi, int(z0[wi]), int(inter[wi]), extra))
        g2_dump.append(dict(
            wit=int(wi), wit_I=list(wit_I[wi]),
            S=sorted(int(x) for x in np.nonzero(SAX[wi])[0]),
            tag=el['tag'], B=list(el['B']), O=list(el['O']),
            sg=list(el['sg']), flip=el['flip'],
            z0=int(z0[wi]), inter=int(inter[wi]), extra=extra,
            extra_in_Tw=[bool(TWb[wi, i]) for i in extra],
            extra_in_Tt=[bool(TTb[mi, i]) for i in extra]))
    dead = eq[:, :32] & eq[:, 32:]                     # 6435 x 32 dead fibers
    expd = SAX & BIX[mi]
    badd = np.nonzero((dead != expd).any(1))[0]
    for wi in badd:
        g3_viol.append((wi, mi,
                        sorted(np.nonzero(dead[wi])[0].tolist()),
                        sorted(np.nonzero(expd[wi])[0].tolist())))
    z0_hist[grp].update(z0.tolist())
    dead_hist[grp].update(dead.sum(1).tolist())
    # ---- menu blind test (G1 general law) on the MEASURED dead loci ----
    keys = dead.astype(np.uint64) @ bitw
    uk, idx, cts = np.unique(keys, return_index=True, return_counts=True)
    F, Nmap, m0, c8 = set(el['F']), el['Nmap'], el['m0'], el['const8']
    fL, nL = len(F), len(Nmap)
    exp_distinct = sum(comb(fL, a) * comb(nL, j)
                       for a in range(fL + 1) for j in range(nL + 1)
                       if 0 <= 8 - a - j <= m0)
    ok = (len(uk) == exp_distinct)
    if ok:
        for u, ix, ct_ in zip(uk, idx, cts):
            Z = set(np.nonzero(dead[ix])[0].tolist())
            if (8 in Z) != c8 or 24 in Z:
                ok = False; break
            a = j = 0
            good = True
            for beta in AX:
                lo, hi = beta in Z, (beta + 16) in Z
                if lo and hi:
                    if beta not in F: good = False; break
                    a += 1
                elif lo or hi:
                    elx = beta if lo else beta + 16
                    if Nmap.get(beta) != elx: good = False; break
                    j += 1
            pred = comb(m0, 8 - a - j) if 0 <= 8 - a - j <= m0 else 0
            if not good or int(ct_) != pred or pred == 0:
                ok = False; break
            mult_menu[grp][pred] += 1
    if ok:
        menu_pass[grp] += 1
    else:
        menu_fail.append((mi, el['tag'], len(uk), exp_distinct))
tick(f"pair tests complete: {NW} witnesses x {M} marginals = {NW*M} pairs")

# ============================================================================
# 5. REPORT
# ============================================================================
def desc_w(wi):
    return f"witness#{wi} I={wit_I[wi]} S={sorted(np.nonzero(SAX[wi])[0].tolist())}"
def desc_m(mi):
    el = pool[mi]
    return (f"marginal#{mi} [{el['tag']}] B={el['B']} O={el['O']} sg={el['sg']} "
            f"flip={el['flip']}")

print("\n========================= G2: EXACTNESS AT n=64 =========================")
print(f"pairs tested: {NW*M:,} ({NW}x{ncen} census + {NW}x{nspur} spurious)")
print(f"violations (|Z0| != |T_w cap T_t|): {len(g2_viol)}")
for wi, mi, z0v, iv, extra in g2_viol:
    print(f"  VIOLATION: {desc_w(wi)}\n    x {desc_m(mi)}\n"
          f"    |Z0|={z0v} |T cap T'|={iv} extra zeros at H-indices {extra}")
print(f"|T_w cap T_t| histogram, census pairs:   {dict(sorted(z0_hist['census'].items()))}")
print(f"|T_w cap T_t| histogram, spurious pairs: {dict(sorted(z0_hist['spurious'].items()))}")

print("\n========================= G3: DICHOTOMY AT n=64 =========================")
print(f"violations (L1 dead fibers != S cap B): {len(g3_viol)}")
for wi, mi, got, exp in g3_viol:
    print(f"  VIOLATION: {desc_w(wi)}\n    x {desc_m(mi)}\n"
          f"    dead={got} S^B={exp}")
print(f"dead-locus |S cap B| histogram, census:   {dict(sorted(dead_hist['census'].items()))}")
print(f"dead-locus |S cap B| histogram, spurious: {dict(sorted(dead_hist['spurious'].items()))}")

print("\n==================== MENU: G1 GENERAL LAW BLIND TEST ====================")
print(f"law: multiplicity of locus (B cap {{8}}) u U_A pairs u U_J singles over the "
      f"6435 witnesses == C(m0, 8-|A|-|J|)")
print(f"census elements passing the full menu (every locus + completeness): "
      f"{menu_pass['census']}/{ncen}")
print(f"spurious elements passing: {menu_pass['spurious']}/{nspur}")
for mi, tag, got, exp in menu_fail:
    print(f"  MENU FAIL: {desc_m(mi)}: {got} distinct loci vs {exp} expected")
print(f"multiplicity values realized (census):   {dict(sorted(mult_menu['census'].items()))}")
print(f"multiplicity values realized (spurious): {dict(sorted(mult_menu['spurious'].items()))}")

summary = dict(
    p=P, n=n, s=s, lam=LAM, witnesses=NW,
    census_solutions=target_sols, census_elements=ncen,
    spurious_solutions=len(SPUR_RAW), spurious_elements=nspur,
    pairs=NW * M,
    g2_violations=len(g2_viol), g3_violations=len(g3_viol),
    menu_pass_census=menu_pass['census'], menu_pass_spurious=menu_pass['spurious'],
    char0_total_reproduced=tot64, feasible_classes=len(feas64),
    n32_calibration=tot32,
    z0_hist_census={int(k): int(v) for k, v in z0_hist['census'].items()},
    z0_hist_spurious={int(k): int(v) for k, v in z0_hist['spurious'].items()},
    dead_hist_census={int(k): int(v) for k, v in dead_hist['census'].items()},
    dead_hist_spurious={int(k): int(v) for k, v in dead_hist['spurious'].items()},
    seed=20260611,
)
out = "/home/nubs/Git/ArkLib/scripts/probes/incidence/rungs/lane_g2g3_n64_summary.json"
json.dump(summary, open(out, "w"), indent=1)
outv = "/home/nubs/Git/ArkLib/scripts/probes/incidence/rungs/lane_g2g3_n64_violations.json"
json.dump(g2_dump, open(outv, "w"), indent=1)
tick(f"summary written: {out}")
tick(f"violation dump written: {outv}")

print("\n=============================== VERDICT ===============================")
v_g2 = "CONFIRMED" if not g2_viol else "REFUTED"
v_g3 = "CONFIRMED" if not g3_viol else "REFUTED"
v_menu = ("CONFIRMED" if menu_pass['census'] == ncen
          and menu_pass['spurious'] == nspur else "REFUTED")
print(f"G2 (exactness at rung 3, n=64): {v_g2} "
      f"({len(g2_viol)} violations / {NW*M:,} pairs; incl. all O134 spurious)")
print(f"G3 (dichotomy generality, n=64): {v_g3} "
      f"({len(g3_viol)} violations)")
print(f"G1 general menu law at s=32: {v_menu} "
      f"({menu_pass['census'] + menu_pass['spurious']}/{M} elements)")
