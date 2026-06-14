#!/usr/bin/env python3
"""Adversarial window probe: (q,n,k,w)=(13,6,1,2). Window check: ladder 3w+k=7 > 6=n
(beyond reach), UDR 2w+k+1=6 <= 6 (at boundary... need n >= 2w+k+1: 6 >= 6 OK below-UDR edge).
k=1: codewords are constants — explainability trivial to check. Heavy sampling over
rational pairs (l deg<=2, R deg<=2) + structured + hill climbing."""
import random
random.seed(42)
q, n, k, w = 13, 6, 1, 2
# domain: 6th roots of unity in F13 (g=4: 4^6=4096=315*13+1 ✓)
g = 4
dom = [pow(g, i, q) for i in range(n)]
assert len(set(dom)) == n
t_min = n - w  # 4
def evalp(co, x):
    a = 0
    for c in reversed(co): a = (a*x + c) % q
    return a
def ratword(l, r):
    out = []
    for x in dom:
        lv = evalp(l, x)
        if lv == 0: return None
        out.append(evalp(r, x) * pow(lv, q-2, q) % q)
    return tuple(out)
def explainable(line):
    # k=1: codeword = constant c; agree on >= 4 of 6 positions
    from collections import Counter
    cnt = Counter(line)
    return cnt.most_common(1)[0][1] >= t_min
def joint_fails(T, u0, u1):
    # both rows must be constant on T
    return len(set(u0[i] for i in T)) > 1 or len(set(u1[i] for i in T)) > 1
def bad_count(u0, u1):
    from itertools import combinations
    cnt = 0
    for gam in range(q):
        line = tuple((u0[i] + gam*u1[i]) % q for i in range(n))
        found = False
        from collections import Counter
        for c, m in Counter(line).most_common():
            if m < t_min: break
            A = [i for i in range(n) if line[i] == c]
            for T in combinations(A, t_min):
                if joint_fails(T, u0, u1): found = True; break
            if found: break
        if found: cnt += 1
    return cnt
def genuine(l, r):
    # l nonconstant and l does not divide r (deg r <= 2 < ... just check r mod l != 0)
    ll = l[:]
    while ll and ll[-1] == 0: ll.pop()
    if len(ll) <= 1: return False
    inv = pow(ll[-1], q-2, q); ll = [(c*inv)%q for c in ll]
    rr = r[:]
    while len(rr) >= len(ll):
        f = rr[-1]
        for i in range(len(ll)): rr[len(rr)-len(ll)+i] = (rr[len(rr)-len(ll)+i] - f*ll[i]) % q
        rr.pop()
    return any(rr)
best = 0; arg = None
N = 30000
for trial in range(N):
    l0 = [random.randrange(q) for _ in range(3)]; r0 = [random.randrange(q) for _ in range(3)]
    l1 = [random.randrange(q) for _ in range(3)]; r1 = [random.randrange(q) for _ in range(3)]
    if not (genuine(l0,r0) and genuine(l1,r1)): continue
    u0 = ratword(l0,r0); u1 = ratword(l1,r1)
    if u0 is None or u1 is None: continue
    c = bad_count(u0,u1)
    if c > best:
        best = c; arg = (u0,u1,l0,r0,l1,r1)
        print(f"trial {trial}: new max {best}  u0={u0} u1={u1}", flush=True)
print(f"\nWINDOW ADVERSARIAL (13,6,1,w=2): max bad over ~{N} genuine rational pairs = {best}", flush=True)
print(f"reference: w+3 = {w+3}", flush=True)
