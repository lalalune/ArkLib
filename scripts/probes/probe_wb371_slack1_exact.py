#!/usr/bin/env python3
"""
Slack-1 exact probe: the maximum graded fiber count at slack 1, exhaustively
over adversarial u-classes.

Setting: deg l0 = w (nonvanishing on D), slack s = 1 (i.e. D_def = 1 deep-window
or z0 = 1 pole-recursion). Graded witnesses:
  j=0: |T| = w,   deg g <= 1
  j=1: |T| = w-1, deg g  = 0 (g constant != 0)
with m_T == u*g (mod l0).

The solution module is dim-3: by CF/Pade structure, solutions are
alpha*(C1) + beta*(C2) for consecutive convergent pairs with deg alpha <= 1.

Instances: (q,n,w) = (23,11,4) [n = 3w-1, mu_11 in F_23] and (13,12,4) at
slack 1 = pole-recursion z0=1 (n=12 first row, punctured n'=11... emulate by
(23,11,4) directly).

Adversarial u: instead of random, build u to ALIGN many m_T in one class:
  u-candidates = m_T0 * g0^{-1} mod l0 over seed pairs (T0, g0) -- then count.
Also random u for comparison. Track max and the extremal member structure.
"""
import itertools, random

q, n, w = 23, 11, 4
SLACK = 1

def order_subgroup(q, n):
    for cand in range(2, q):
        seen = set(); x = 1
        for _ in range(q - 1):
            x = (x * cand) % q; seen.add(x)
        if len(seen) == q - 1:
            g = cand; break
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, j, q) for j in range(n)})

D = order_subgroup(q, n)

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def poleval(p, x):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def polmod(a, b):
    a = [x % q for x in a]
    db = max(i for i in range(len(b)) if b[i] % q)
    inv = pow(b[db], q - 2, q)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % q
        if c:
            f = (c * inv) % q
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % q
    out = [x % q for x in a[:db]]
    return out + [0] * (db - len(out))

def polinv_mod(u, l0):
    # extended euclid
    def deg(p):
        d = -1
        for i in range(len(p)):
            if p[i] % q: d = i
        return d
    r0, r1 = l0[:], u[:]
    t0, t1 = [0], [1]
    while deg(r1) > 0 or (deg(r1) == 0):
        if deg(r1) < 0:
            break
        if deg(r1) == 0:
            break
        d0, d1 = deg(r0), deg(r1)
        if d0 < d1:
            r0, r1, t0, t1 = r1, r0, t1, t0
            continue
        c = (r0[d0] * pow(r1[d1], q - 2, q)) % q
        k = d0 - d1
        rs = [0] * k + [(x * c) % q for x in r1]
        r0 = [( (r0[i] if i < len(r0) else 0) - (rs[i] if i < len(rs) else 0)) % q
              for i in range(max(len(r0), len(rs)))]
        ts = [0] * k + [(x * c) % q for x in t1]
        t0 = [( (t0[i] if i < len(t0) else 0) - (ts[i] if i < len(ts) else 0)) % q
              for i in range(max(len(t0), len(ts)))]
    dr = deg(r1)
    if dr != 0:
        return None
    ginv = pow(r1[0], q - 2, q)
    return polmod([(x * ginv) % q for x in t1], l0)

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % q, 1])
    return out

def graded_members(l0, uinv):
    """uinv = u^{-1} mod l0. member (T, g): m_T*uinv mod l0 has deg <= budget."""
    members = []
    for j in range(SLACK + 1):
        size = w - j
        budget = SLACK - j
        for T in itertools.combinations(D, size):
            rep = polmod(polmul(m_of(T), uinv), l0)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr == -1:
                continue
            if dr <= budget:
                members.append((T, dr))
    return members

random.seed(53)
print(f"(q,n,w) = ({q},{n},{w}), slack {SLACK}, D = mu_{n}: {D}")
pool = []
while len(pool) < 40:
    l0 = [random.randrange(q) for _ in range(w)] + [1]
    if all(poleval(l0, x) for x in D):
        pool.append(l0)

best = (0, None, None)
for l0 in pool[:25]:
    # adversarial u-classes: u = m_T0 / g0 for seeds => that member is in the
    # fiber automatically; vary seeds. u = m_T0 * (a+bX)^{-1}: but simpler
    # u^{-1} = g0 * m_T0^{-1}: we only need uinv: uinv = g0 * inv(m_T0)
    seen_u = set()
    cand_uinv = []
    for T0 in itertools.combinations(D, w):
        invm = polinv_mod(list(m_of(T0)), l0)
        if invm is None:
            continue
        for g0 in ([1], [0, 1], [1, 1]):
            uinv = polmod(polmul(invm, g0), l0)
            tu = tuple(uinv)
            if tu not in seen_u:
                seen_u.add(tu)
                cand_uinv.append(uinv)
    # also random
    for _ in range(120):
        uinv = [random.randrange(q) for _ in range(w)]
        if any(x % q for x in uinv):
            cand_uinv.append(uinv)
    for uinv in cand_uinv:
        mem = graded_members(l0, uinv)
        if len(mem) > best[0]:
            best = (len(mem), l0, mem)
print(f"\nMAX graded slack-1 count = {best[0]}")
if best[1]:
    print(f"  l0 = {best[1]}")
    for T, dg in best[2][:14]:
        print(f"    T={T} (deg g = {dg})")
    # structure: pairwise intersections
    Ts = [set(T) for T, _ in best[2]]
    if len(Ts) > 1:
        ints = [len(a & b) for a, b in itertools.combinations(Ts, 2)]
        print(f"  pairwise |Ti ∩ Tj|: max={max(ints)}, distribution={sorted(set(ints))}")
        union = set().union(*Ts)
        print(f"  |union| = {len(union)} of n={n}")
