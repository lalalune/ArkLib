#!/usr/bin/env python3
"""
G3 probe v2 — the GRADED fiber count (the degree-true witness space).

A deep-window witness at row D_def = 3w+k-1-n (k=1) with complement size
|T| = w - j (j >= 0) must satisfy:
   (i)  deg g <= D_def - j   (top-degree matching of the exact identity)
   (ii) m_T == u * g (mod l0)  for the stack-fixed unit class u
So legitimate witnesses = union over j of {T : |T| = w-j,
     exists g, deg g <= D_def - j, m_T == u*g mod l0}.

Count them per (l0, u); conjecture G3-c: graded count <= (D_def+1) + n/w-ish
(the observed bad caps: <= w+1 everywhere).

Also: adversarially choose u to maximize (u ranges over (F[X]/l0)^*; sample).
Scales: (11,10,4) D_def=2; (13,12,4) D_def=2(n'=12? n=12: D_def=3w-n=0...)
  NOTE: D_def = 3w - n for k=1: (11,10,4): 2; (13,10,4)?? mu_10 needs 10|q-1: q=11,31,41...
  use (31,10,4): D_def = 2; and (13,12,4): D_def = 0 (sanity: pencil case).
  and (31,15,4)? 15 | 30 yes: n=15: D_def=3*4-15<0 -> not window. (31,10,5): D_def=5: window
  needs n >= 2w+k+1 = 12 > 10 NO. (31,10,4): 2w+k+1=10<=10<=3w+k-1=12: D_def=2 ok.
"""
import itertools, random

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

def poleval(p, x, q):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

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
    out = [x % q for x in a[:db]]
    return out + [0] * (db - len(out))

def m_of(T, q):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % q, 1], q)
    return out

def solve_graded(l0, u, D_def, q, n, w, D):
    """for each j and each T (|T| = w-j), check: exists g deg <= D_def - j with
       m_T == u*g mod l0.  Reduce: m_T * u^{-1} mod l0 must be expressible as g
       i.e. the class c := m_T * u^{-1} mod l0 must contain a poly of deg <= D_def-j
       -- but class reps mod l0 have deg < deg l0 = w; condition: the canonical
       rep has deg <= D_def - j (the rep IS unique of deg < w)."""
    w0 = max(i for i in range(len(l0)) if l0[i] % q)
    # u^{-1} mod l0 via extended Euclid over F_q[X]
    def polgcdext(a, b):
        # returns (g, s, t) with s*a + t*b = g
        r0, r1 = a[:], b[:]
        s0, s1 = [1], [0]
        t0, t1 = [0], [1]
        def deg(p):
            d = -1
            for i in range(len(p)):
                if p[i] % q: d = i
            return d
        def polsub(x, y):
            m = max(len(x), len(y))
            return [( (x[i] if i < len(x) else 0) - (y[i] if i < len(y) else 0)) % q for i in range(m)]
        def polshift(p, k):
            return [0]*k + p
        def polscale(p, c):
            return [(x*c) % q for x in p]
        while deg(r1) >= 0:
            d0, d1 = deg(r0), deg(r1)
            if d0 < d1:
                r0, r1, s0, s1, t0, t1 = r1, r0, s1, s0, t1, t0
                continue
            c = (r0[deg(r0)] * pow(r1[deg(r1)], q-2, q)) % q
            k = deg(r0) - deg(r1)
            r0 = polsub(r0, polshift(polscale(r1, c), k))
            s0 = polsub(s0, polshift(polscale(s1, c), k))
            t0 = polsub(t0, polshift(polscale(t1, c), k))
        return r0, s0, t0
    g0, s, t = polgcdext(u, l0)
    dg = max((i for i in range(len(g0)) if g0[i] % q), default=-1)
    if dg != 0:
        return None  # u not invertible mod l0 (shouldn't happen for good u)
    ginv = pow(g0[0], q - 2, q)
    uinv = [(x * ginv) % q for x in s]  # s/g0 = u^{-1} mod l0
    uinv = polmod(uinv, l0, q)
    members = []
    for j in range(0, D_def + 1):
        size = w - j
        if size < 1:
            continue
        gbudget = D_def - j
        for T in itertools.combinations(D, size):
            mT = m_of(T, q)
            rep = polmod(polmul(mT, uinv, q), l0, q)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr == -1:
                continue  # zero class: l0 | m_T impossible (nonvanishing)
            if dr <= gbudget:
                members.append((T, dr))
    return members

random.seed(41)
for (q, n, w) in [(31, 10, 4), (13, 12, 4), (11, 10, 4)]:
    D = order_subgroup(q, n)
    D_def = 3 * w - n
    if D_def < 0:
        print(f"(q,n,w)=({q},{n},{w}): not in window (D_def={D_def}), skip")
        continue
    print(f"\n=== (q,n,w)=({q},{n},{w}), D_def={D_def}, budget-conj (D_def+1)+n//w = {(D_def+1)+n//w}, w+1={w+1} ===")
    pool = []
    tries = 0
    while len(pool) < 150 and tries < 200000:
        tries += 1
        l0 = [random.randrange(q) for _ in range(w)] + [1]
        if all(poleval(l0, x, q) for x in D):
            pool.append(l0)
    mx = 0; arg = None
    for trial in range(400):
        l0 = random.choice(pool)
        u = [random.randrange(q) for _ in range(w)]
        if all(c % q == 0 for c in u):
            continue
        mem = solve_graded(l0, u, D_def, q, n, w, D)
        if mem is None:
            continue
        if len(mem) > mx:
            mx = len(mem); arg = (l0, u, mem)
    print(f"  max GRADED fiber count over 400 samples = {mx}")
    if arg:
        print(f"    l0={arg[0]}")
        for T, dg in arg[2][:12]:
            print(f"      T={T} (g-deg {dg})")
