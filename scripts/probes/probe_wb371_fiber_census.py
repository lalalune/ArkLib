#!/usr/bin/env python3
"""
f*(n,w): max number of (n-w)-subset vanishing polynomials m_S pairwise
PROPORTIONAL modulo a single degree-<=w modulus l0 with NO roots in D
(stratum-G locator).  Stratum-G theorem: bad <= |fiber| <= f*.

Scale 1: (13,6,2): 15 quartics, moduli = monic quadratics & linears nonvanishing
on mu_6, plus constants excluded (trivial all-proportional? mod const => quotient
trivial -- excluded: l0 constant handled separately).
Scale 2: (13,12,4): 495 octics, moduli = monic deg<=4 nonvanishing on mu_12
(13^4 = 28561 quartics -> filter no-roots ~ (12/13)^... sample + structured).
Also track WHICH families attain the max (coset/sigma structure?).
"""
import itertools, random
from collections import defaultdict

def order_subgroup(q, n):
    for cand in range(2, q):
        seen = set(); x = 1
        for _ in range(q - 1):
            x = (x * cand) % q; seen.add(x)
        if len(seen) == q - 1:
            g = cand; break
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, j, q) for j in range(n)})

def polmul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def polmod(a, b, q):
    a = [x % q for x in a]
    db = max(i for i in range(len(b)) if b[i] % q)
    inv = pow(b[db], q - 2, q)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % q
        if c:
            f = (c * inv) % q
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % q
    out = tuple(x % q for x in a[:db])
    return out if out else (0,)

def poleval(p, x, q):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def proj_norm(v, q):
    for x in v:
        if x % q:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    return None

def fstar(q, n, w, moduli, SUBS, MS, report_top=3):
    best = (0, None, None)
    for l0 in moduli:
        buckets = defaultdict(list)
        for S in SUBS:
            r = polmod(list(MS[S]), l0, q)
            pn = proj_norm(r, q)
            if pn is None:
                # l0 | m_S: l0 has roots in S? but l0 nonvanishing on D -> impossible
                # unless deg... record specially
                buckets["ZERO"].append(S)
            else:
                buckets[pn].append(S)
        for key, fam in buckets.items():
            if len(fam) > best[0]:
                best = (len(fam), tuple(l0), [tuple(s) for s in fam[:8]], key)
    return best

# ---------------- scale 1 ----------------
q, n, w = 13, 6, 2
D = order_subgroup(q, n)
SUBS = list(itertools.combinations(D, n - w))
MS = {S: tuple(__import__('functools').reduce(lambda a, x: polmul(a, [(-x) % q, 1], q), S, [1])) for S in SUBS}
moduli = []
for a in range(q):
    for b in range(q):
        l = [a, b, 1]
        if all(poleval(l, x, q) for x in D):
            moduli.append(l)
for a in range(q):
    l = [a, 1]
    if all(poleval(l, x, q) for x in D):
        moduli.append(l)
print(f"scale 1 (13,6,2): D={D}, #moduli={len(moduli)}, #S={len(SUBS)}")
b1 = fstar(q, n, w, moduli, SUBS, MS)
print(f"  f*(6,2) = {b1[0]}  attained at l0={b1[1]}")
print(f"  family S's: {b1[2]}")
print(f"  family T's: {[tuple(sorted(set(D)-set(s))) for s in b1[2]]}")

# ---------------- scale 2 ----------------
q2, n2, w2 = 13, 12, 4
D2 = order_subgroup(q2, n2)
SUBS2 = list(itertools.combinations(D2, n2 - w2))
import functools
MS2 = {S: tuple(functools.reduce(lambda a, x: polmul(a, [(-x) % q2, 1], q2), S, [1])) for S in SUBS2}
print(f"\nscale 2 (13,12,4): #S={len(SUBS2)}")

random.seed(17)
moduli2 = []
# exhaustive over monic quartics with no roots in D2 is 13^4=28561*eval cost: ok-ish
cnt = 0
for a in range(q2):
    for b in range(q2):
        for c in range(q2):
            for d in range(q2):
                l = [a, b, c, d, 1]
                ok = True
                for x in D2:
                    if poleval(l, x, q2) == 0:
                        ok = False; break
                if ok:
                    moduli2.append(l)
print(f"  #genuine quartic moduli = {len(moduli2)}")
# fstar over all of them is len(moduli2)*495 polmods ~ 7M -- heavy; sample half
random.shuffle(moduli2)
sel = moduli2[:6000]
b2 = fstar(q2, n2, w2, sel, SUBS2, MS2)
print(f"  f*(12,4) over {len(sel)} sampled moduli = {b2[0]}  at l0={b2[1]}")
print(f"  family T's: {[tuple(sorted(set(D2)-set(s))) for s in b2[2]]}")
