#!/usr/bin/env python3
"""
No-core slack-1 probe: max graded fiber size among configurations WITHOUT a
chain core, at (23,11,4) and (13,11,4)... 11 | q-1: q in {23, 67, 89}; use 23, 67.

Core test: a (w-1)-set K is a core iff the class u^{-1}*m_K mod l0 has a
degree-0 lift (i.e. canonical rep is a nonzero constant).
No-core configurations: count full-size members (deg g <= 1) + small members.
Conjecture: no-core total <= 3 (vs chain configurations reaching ~n).
Also track whether full members pairwise intersect <= 1 (dichotomy check).
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

def run(q, n, w, NTRIAL=600, NL=40):
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
    def m_of(T):
        out = [1]
        for x in T:
            out = polmul(out, [(-x) % q, 1])
        return out
    def polinv_mod(u, l0):
        def deg(p):
            d = -1
            for i in range(len(p)):
                if p[i] % q: d = i
            return d
        r0, r1 = l0[:], u[:]
        t0, t1 = [0], [1]
        while deg(r1) > 0:
            d0, d1 = deg(r0), deg(r1)
            if d0 < d1:
                r0, r1, t0, t1 = r1, r0, t1, t0
                continue
            c = (r0[d0] * pow(r1[d1], q - 2, q)) % q
            k = d0 - d1
            rs = [0] * k + [(x * c) % q for x in r1]
            r0 = [((r0[i] if i < len(r0) else 0) - (rs[i] if i < len(rs) else 0)) % q
                  for i in range(max(len(r0), len(rs)))]
            ts = [0] * k + [(x * c) % q for x in t1]
            t0 = [((t0[i] if i < len(t0) else 0) - (ts[i] if i < len(ts) else 0)) % q
                  for i in range(max(len(t0), len(ts)))]
        if deg(r1) != 0:
            return None
        ginv = pow(r1[max(i for i in range(len(r1)) if r1[i] % q)], q - 2, q)
        return polmod([(x * ginv) % q for x in t1], l0)

    random.seed(61)
    pool = []
    while len(pool) < NL:
        l0 = [random.randrange(q) for _ in range(w)] + [1]
        if all(poleval(l0, x) for x in D):
            pool.append(l0)
    K_SETS = list(itertools.combinations(D, w - 1))
    T_FULL = list(itertools.combinations(D, w))
    best_nocore = (0, None)
    chain_seen = 0
    for trial in range(NTRIAL):
        l0 = random.choice(pool)
        uinv = [random.randrange(q) for _ in range(w)]
        if not any(x % q for x in uinv):
            continue
        # core check: K is a core iff rep(m_K * uinv) is a nonzero constant
        has_core = False
        for K in K_SETS:
            rep = polmod(polmul(m_of(K), uinv), l0)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr == 0:
                has_core = True
                break
        members = []
        for T in T_FULL:
            rep = polmod(polmul(m_of(T), uinv), l0)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr != -1 and dr <= 1:
                members.append(T)
        smalls = []
        for K in K_SETS:
            rep = polmod(polmul(m_of(K), uinv), l0)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr == 0:
                smalls.append(K)
        total = len(members) + len(smalls)
        if has_core:
            chain_seen += 1
        else:
            if total > best_nocore[0]:
                ints = [len(set(a) & set(b))
                        for a, b in itertools.combinations(members, 2)]
                best_nocore = (total, (l0, members, smalls,
                                       sorted(set(ints)) if ints else []))
    print(f"(q,n,w)=({q},{n},{w}): trials={NTRIAL}, cored-configs={chain_seen}")
    print(f"  NO-CORE max (full+small) = {best_nocore[0]}")
    if best_nocore[1]:
        l0, members, smalls, ints = best_nocore[1]
        print(f"  members={members} smalls={smalls} pairwise-int set={ints}")

run(23, 11, 4)
run(67, 11, 4)
