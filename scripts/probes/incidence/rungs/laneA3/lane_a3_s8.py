#!/usr/bin/env python3
"""LANE A3 (rigidity across the lambda family) — s=8 leg (n=16), exhaustive.

Pre-registered in rungs/HYPOTHESES.md (A3): char-0/exactness rigidity should hold for
EVERY word, not just the canonical max-fiber configuration. This leg varies the word
w(x) = x^10 + lam*x^8 across the lambda family at n=16 and measures, for the COMPLETE
agree>=9 list of each word, the zero-excess law |Z0(c-c')| = |T cap T'| on ALL pairs.

Method (all exact mod P = BabyBear, no sampling):
  1. e1 census of 5-subsets of mu_8 (C(8,5)=56): distinct values + fiber sizes.
     Witness-layer prediction for lam: fiber size of e1 at z = -lam (u_S(X^2) anatomy).
  2. Lambda panel ACROSS fiber sizes: canonical (fiber 3, gate 19=3+16), the other
     fiber-3 values, fiber-1 values, fiber-0 controls (lam with no witness layer).
  3. Per lambda: FULL C(16,9)=11440 sweep — every 9-subset of the domain, deg<8
     interpolant test -> complete deduped list with agreement sets (ground truth,
     anatomy-free).
  4. ALL pairwise checks: Z0 = coordinate matches of the two evaluation vectors
     (exact zero set of the difference on mu_16); excess = |Z0| - |T cap T'|.
     Layer-resolved histograms (W-W / W-D / D-D); every excess pair identified.

Conventions: P=2013265921, g0=31, H = mu_16 via h = g0^((P-1)/16), squares G8 = mu_8,
z* = h^4, canonical lam = P - z* = 284861408 (O129/RESULTS-INCIDENCE).
"""
import sys
from itertools import combinations
from collections import Counter

P = 2013265921; G0 = 31
N, KDEG, S = 16, 8, 8          # domain size, code degree bound, rung s
CANON = 284861408

def pmul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[i+j] = (out[i+j] + x*y) % P
    return out

def interp(xs, ys):
    n = len(xs); out = [0]*n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = pmul(num, [(-xs[j]) % P, 1])
            den = den * ((xs[i]-xs[j]) % P) % P
        s = ys[i] * pow(den, P-2, P) % P
        for d in range(len(num)): out[d] = (out[d] + s*num[d]) % P
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out

def peval(c, x):
    r = 0
    for co in reversed(c): r = (r*x + co) % P
    return r

h = pow(G0, (P-1)//N, P)
H = [pow(h, i, P) for i in range(N)]
G8 = [pow(h*h % P, i, P) for i in range(N//2)]
zstar = pow(h, S//2, P)
assert (P - zstar) % P == CANON

# ---- 1. e1 census over 5-subsets of mu_8 ----
fib = Counter()
for sub in combinations(G8, 5): fib[sum(sub) % P] += 1
hist = Counter(fib.values())
print(f"e1 census, 5-subsets of mu_8: {sum(fib.values())} subsets, "
      f"{len(fib)} distinct values, fiber-size histogram {dict(sorted(hist.items()))}")
maxfib_vals = sorted(v for v, c in fib.items() if c == max(fib.values()))
print(f"fiber-3 e1 values: {maxfib_vals}")
print(f"fiber-3 values == mu_8 sorted? {maxfib_vals == sorted(G8)}")
print(f"canonical: z* = {zstar} (fiber {fib[zstar]}), lam = {CANON}")

# ---- 2. lambda panel ----
f3 = sorted(v for v, c in fib.items() if c == 3)
f1 = sorted(v for v, c in fib.items() if c == 1)
panel = []
panel.append(("canonical f3", CANON))                       # e1 = z*
for v in f3:
    if v != zstar and len([p for p in panel if p[0].startswith("f3")]) < 2:
        panel.append((f"f3 e1={v}", (P - v) % P))
for v in f1[:5]:
    panel.append((f"f1 e1={v}", (P - v) % P))
# fiber-0 controls: lam such that -lam is NOT an e1 value
f0 = []
x = 2
while len(f0) < 2:
    if x not in fib and x not in f0: f0.append(x)
    x += 1
for v in f0:
    panel.append((f"f0 e1={v}", (P - v) % P))
print(f"\nlambda panel ({len(panel)} words):")
for tag, lam in panel: print(f"  {tag:24s} lam={lam}")

# ---- 3+4. per-lambda full sweep + all-pairs exactness ----
def sweep(lam):
    w = [(pow(x, S+2, P) + lam*pow(x, S, P)) % P for x in H]
    found = {}
    for sub in combinations(range(N), S+1):
        c = interp([H[i] for i in sub], [w[i] for i in sub])
        if len(c) <= KDEG:
            ev = tuple(peval(c, x) for x in H)
            if ev not in found:
                found[ev] = frozenset(i for i in range(N) if ev[i] == w[i])
    return w, found

def neg_vec(ev):
    # c(-X) evaluations: index i -> i+8 mod 16
    return tuple(ev[(i + N//2) % N] for i in range(N))

grand = Counter(); grand_pairs = 0
summary = []
for tag, lam in panel:
    w, found = sweep(lam)
    items = sorted(found.items())
    agree_hist = Counter(len(a) for _, a in items)
    wit = [(ev, a) for ev, a in items if len(a) == S+2]
    den = [(ev, a) for ev, a in items if len(a) == S+1]
    pred = fib.get((P - lam) % P, 0)
    ok_wit = (len(wit) == pred)
    # all pairs, layer-resolved
    ex = {"W-W": Counter(), "W-D": Counter(), "D-D": Counter()}
    bad = []
    for (e1v, a1), (e2v, a2) in combinations(items, 2):
        z0 = sum(1 for i in range(N) if e1v[i] == e2v[i])
        tt = len(a1 & a2)
        lay = ("W" if len(a1) == S+2 else "D") + "-" + ("W" if len(a2) == S+2 else "D")
        if lay == "D-W": lay = "W-D"
        ex[lay][z0 - tt] += 1
        grand[z0 - tt] += 1; grand_pairs += 1
        if z0 != tt:
            extras = [i for i in range(N) if e1v[i] == e2v[i] and not (i in a1 and i in a2)]
            bad.append((lay, z0 - tt, extras, e2v == neg_vec(e1v)))
    npairs = len(items)*(len(items)-1)//2
    print(f"\n== {tag} lam={lam} ==")
    print(f"list = {len(items)} (agreement hist {dict(sorted(agree_hist.items()))}); "
          f"witness count {len(wit)} vs e1-fiber prediction {pred} -> "
          f"{'MATCH' if ok_wit else 'MISMATCH'}")
    print(f"pairs = {npairs}; excess histograms: "
          + "; ".join(f"{k} {dict(sorted(v.items()))}" for k, v in ex.items() if v))
    for lay, e, extras, isneg in bad:
        print(f"  EXCESS pair [{lay}] +{e} at idx {extras} negation={isneg}")
    if tag == "canonical f3":
        gate = (len(items) == 19 and len(wit) == 3 and len(den) == 16)
        print(f"GATE canonical 19=3+16: {'PASS' if gate else 'FAIL'}")
        if not gate: sys.exit(1)
    summary.append((tag, lam, len(wit), len(den), len(items), npairs,
                    sum(c for e, c in grand.items() if e > 0 and False)))
    summary[-1] = (tag, lam, len(wit), len(den), len(items), npairs,
                   sum(c for e, c in ex["W-W"].items() if e > 0)
                   + sum(c for e, c in ex["W-D"].items() if e > 0)
                   + sum(c for e, c in ex["D-D"].items() if e > 0))

print("\n==== SUMMARY (s=8, exhaustive sweeps, ALL pairs) ====")
print(f"{'word':24s} {'lam':>11s} {'wit':>4s} {'marg':>5s} {'list':>5s} {'pairs':>6s} {'excess>0':>9s}")
for tag, lam, nw, nd, nl, npr, nbad in summary:
    print(f"{tag:24s} {lam:11d} {nw:4d} {nd:5d} {nl:5d} {npr:6d} {nbad:9d}")
print(f"\nGRAND TOTAL pairs {grand_pairs}, excess histogram {dict(sorted(grand.items()))}")
