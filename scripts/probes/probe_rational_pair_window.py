#!/usr/bin/env python3
"""The genuine rational-pair window: (q,n,k,w)=(97,16,2,5) — between ladder reach
(3w+k-1 >= n: w >= 5) and UDR (w <= 6). For GENUINE rational rows joint always fails
(degree-forcing), so bad <=> line explainable. Count exact bad gammas."""
import random
random.seed(371)
q, n, k, g, w = 97, 16, 2, None, 5
# find generator of order-16 subgroup: g16 with g16^16=1, primitive
for cand in range(2, 97):
    if pow(cand, 16, q) == 1 and pow(cand, 8, q) != 1:
        g = cand; break
dom = [pow(g, i, q) for i in range(n)]
assert len(set(dom)) == n
t_min = n - w  # 11
def evalpoly(co, x):
    a = 0
    for c in reversed(co): a = (a*x + c) % q
    return a
def rational_word(lco, rco):
    out = []
    for x in dom:
        lv = evalpoly(lco, x)
        if lv == 0: return None
        out.append(evalpoly(rco, x) * pow(lv, q-2, q) % q)
    return tuple(out)
def genuine(lco, rco):
    # l does not divide r: check r mod l != 0 (l monic-ized, deg l = len-1 with top nonzero)
    l = lco[:]; r = rco[:]
    while l and l[-1] == 0: l.pop()
    if len(l) <= 1: return False  # constant denominator => polynomial
    inv = pow(l[-1], q-2, q)
    l = [(c*inv) % q for c in l]
    r = r[:]
    while len(r) >= len(l):
        f = r[-1]
        for i in range(len(l)):
            r[len(r)-len(l)+i] = (r[len(r)-len(l)+i] - f*l[i]) % q
        r.pop()
    return any(r)
def bad_count_fast(u0, u1):
    # bad <=> exists codeword (a+bx) within distance w of the line (genuine rows => no joint)
    cnt = 0
    for gam in range(q):
        line = [(u0[i] + gam*u1[i]) % q for i in range(n)]
        found = False
        # candidate c determined by any 2 agreement points; try pairs (i,j) of positions
        for i in range(n):
            if found: break
            for j in range(i+1, n):
                xi, xj = dom[i], dom[j]
                b = (line[i] - line[j]) * pow(xi - xj, q-2, q) % q
                a = (line[i] - b*xi) % q
                d = sum(1 for t in range(n) if (a + b*dom[t]) % q != line[t])
                if d <= w: found = True; break
        if found: cnt += 1
    return cnt
best = 0; tried = 0; arg = None
while tried < 60:
    l0 = [random.randrange(q) for _ in range(w+1)]; r0 = [random.randrange(q) for _ in range(w+k)]
    l1 = [random.randrange(q) for _ in range(w+1)]; r1 = [random.randrange(q) for _ in range(w+k)]
    if not (genuine(l0, r0) and genuine(l1, r1)): continue
    u0 = rational_word(l0, r0); u1 = rational_word(l1, r1)
    if u0 is None or u1 is None: continue
    tried += 1
    c = bad_count_fast(u0, u1)
    if c > best: best = c; arg = "random"
    if tried % 20 == 0: print(f"...{tried} tried, max {best}", flush=True)
print(f"random genuine rational pairs (w=5 window): max bad = {best}", flush=True)
# structured: shared denominator + KKH26-flavor numerators
best_s = 0
for trial in range(40):
    l = [random.randrange(q) for _ in range(w+1)]
    r0 = [random.randrange(q) for _ in range(w+k)]
    r1 = [random.randrange(q) for _ in range(w+k)]
    if not (genuine(l, r0) and genuine(l, r1)): continue
    u0 = rational_word(l, r0); u1 = rational_word(l, r1)
    if u0 is None or u1 is None: continue
    c = bad_count_fast(u0, u1)
    if c > best_s: best_s = c
print(f"shared-denominator pairs: max bad = {best_s}", flush=True)
print(f"reference: w+3 = {w+3}, q = {q}", flush=True)
