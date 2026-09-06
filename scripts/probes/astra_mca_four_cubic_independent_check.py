#!/usr/bin/env python3
"""Independent exact field, polynomial, and same-support four-cubic controls."""
import json
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
f = [[327488682710052383823156554057047840665626746782, 237475201196817860974031760546692142896192504609, 123759034962286266337578740424093841491820757632, 42027899796294947967075361330307685186643122885], [37886726622673345727764654122022914454514819173, 161701747951471169518502452302646313987162866265, 207814834554876162271729463084709211865107003400, 323347509536430781583845846848763069933498443070], [209631343301899186947392826726164768529126696091, 127900208135907868576889447632378612223949061346, 241616374370439463213342467754976913628320808323, 151602892857204940364217674244621215858886566148], [151602892857204940364217674244621215858886566148, 123759034962286266337578740424093841491820757630, 237475201196817860974031760546692142896192504607, 209631343301899186947392826726164768529126696091]]

def trim(a):
    a = [x % P for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def sub(a, b):
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b)))])

def mul(a, b):
    z = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            z[i + j] = (z[i + j] + x * y) % P
    return trim(z)

def rem(a, b):
    a = trim(a)
    b = trim(b)
    while a != [0] and len(a) >= len(b):
        q = a[-1] * pow(b[-1], -1, P) % P
        j = len(a) - len(b)
        for i, v in enumerate(b):
            a[i + j] = (a[i + j] - q * v) % P
        a = trim(a)
    return a

def gcd(a, b):
    while b != [0]:
        a, b = (b, rem(a, b))
    return [0] if a == [0] else [x * pow(a[-1], -1, P) % P for x in a]

def ev(a, x):
    z = 0
    for t in a[::-1]:
        z = (z * x + t) % P
    return z
w = [sub(x, f[0]) for x in f]
z = [0]
for x in w:
    z = gcd(z, x)
assert z == [1]
eta = pow(G, 2 ** 27, P)
assert pow(eta, 8, P) == 1 and pow(eta, 4, P) == P - 1
v = [[ev(x, pow(eta, j, P)) for x in w] for j in range(8)]
parts = []
for vv in v:
    groups = {}
    for i, x in enumerate(vv):
        groups.setdefault(x, []).append(i)
    parts.append(list(groups.values()))
expected = [[[0, 1, 2], [3]], [[0, 1, 3], [2]], [[0, 3], [1], [2]], [[0, 2, 3], [1]], [[0, 2], [1], [3]], [[0, 1], [2], [3]], [[0], [1, 2, 3]], [[0], [1, 2, 3]]]
assert parts == expected
for i in range(4):
    for j in range(i):
        diff = sub(w[i], w[j])
        roots = [r for r in range(8) if v[r][i] == v[r][j]]
        fac = [1]
        for r in roots:
            fac = mul(fac, [-pow(eta, r, P), 1])
        assert len(roots) == 3 and diff == [diff[-1] * a % P for a in fac]
beta = [5, 5, 3, 5, 3, 3, 7, 7]
for j, partition in enumerate(parts):
    assert len(partition) <= beta[j]
    assert all((1 + 2 * len(set(group) & {1, 2, 3}) <= beta[j] for group in partition))
    assert 6 <= beta[j] + 3
assert sum(beta) == 38

def counts(s):
    A = 11 * s // 2 - 2
    n = 8 * s
    R = s - 2
    owners = [(0, [0, 1, 2], s), (1, [0, 1, 3], s), (2, [0, 3], s // 2), (3, [0, 2, 3], s), (4, [0, 2], s // 2), (5, [0, 1], s // 2), (6, [1, 2, 3], s), (7, [1, 2, 3], s)]
    cores = [R + sum((c for j, ids, c in owners if i in ids)) for i in range(4)]
    assert cores == [A] * 4
    D = sum((c for j, ids, c in owners)) + 3 * (s // 2 + 2)
    assert D == n + 6
    return dict(n=n, s=s, k=4 * s, common_roots=R, cores=cores, agreement=A + 1, bad_count=D, error_numerator=n - A - 1, security_margin=D * 2 ** 128 - P)

def dense(s):
    n = 8 * s
    k = 4 * s
    A = 11 * s // 2 - 2
    g = pow(G, 2 ** 30 // n, P)
    xs = [pow(g, t, P) for t in range(n)]
    assert len(set(xs)) == n and pow(g, n, P) == 1
    fibers = [[t for t in range(n) if t % 8 == j] for j in range(8)]
    roots = fibers[4][s // 2:s - 1] + fibers[5][s // 2:s - 1]
    assert len(roots) == s - 2
    B = [1]
    for t in roots:
        B = mul(B, [-xs[t], 1])
    ps = []
    for wi in w:
        wi_comp = [0] * (s * (len(wi) - 1) + 1)
        for h, c in enumerate(wi):
            wi_comp[s * h] = c
        pi = mul(B, wi_comp)
        assert len(pi) <= k - 1
        ps.append(pi)
    pv = [[ev(pi, x) for x in xs] for pi in ps]
    assert {t for t in range(n) if all((pv[i][t] == 0 for i in range(4)))} == set(roots)
    u = [None] * n
    owners = {0: [0, 1, 2], 1: [0, 1, 3], 2: [0, 3], 3: [0, 2, 3], 4: [0, 2], 5: [0, 1], 6: [1, 2, 3], 7: [1, 2, 3]}
    uncov = []
    covered = []
    for j, ts in enumerate(fibers):
        for h, t in enumerate(ts):
            x = xs[t]
            if t in roots:
                u[t] = (0, 0)
            elif j == 2 and h >= s // 2 or (j in [4, 5] and h == s - 1):
                uncov.append(t)
            else:
                p = pv[owners[j][0]][t]
                u[t] = (p, x * p % P)
                covered.append(t)
    reserved = {-pow(x, -1, P) % P for x in xs}
    used = set(reserved)
    wits = []
    for t in covered:
        gam = -pow(xs[t], -1, P) % P
        i = next((i for i in range(4) if pv[i][t] != u[t][0]))
        wits.append((gam, i, t))
    for t in uncov:
        x = xs[t]
        vals = {pv[i][t]: i for i in range(4)}
        assert len(vals) == 3
        c = 0
        while True:
            local = []
            for val, i in vals.items():
                num = (c - val) % P
                den = (x * num + 1) % P
                if not den:
                    break
                gamma = -num * pow(den, -1, P) % P
                if gamma in used:
                    break
                local.append((gamma, i, t))
            if len(local) == 3:
                break
            c += 1
        u[t] = (c, (x * c + 1) % P)
        used.update((gam for gam, _, _ in local))
        wits += local
    assert len(wits) == n + 6 and len({a for a, _, _ in wits}) == n + 6
    cores = [{t for t, x in enumerate(xs) if u[t] == (pv[i][t], x * pv[i][t] % P)} for i in range(4)]
    assert [len(c) for c in cores] == [A] * 4 and A >= k
    for gam, i, t in wits:
        assert t not in cores[i]
        agreements = {j for j, x in enumerate(xs) if (u[j][0] + gam * u[j][1] - (1 + gam * x) * pv[i][j]) % P == 0}
        assert agreements == cores[i] | {t}
        assert u[t] != (pv[i][t], xs[t] * pv[i][t] % P)
    return {'n': n, 'core': A, 'witness_checks': len(wits), 'gcd_degree': len(B) - 1, 'finite_unique': True}
result = {'source_degree': [len(p) - 1 for p in f], 'primitive_gcd': z, 'partitions': parts, 'production': counts(2 ** 27), 'dense': [dense(8), dense(16)]}
assert result['production']['error_numerator'] == 335544321
assert result['production']['security_margin'] > 0
s = 2 ** 27
A = result['production']['cores'][0]
assert 41 * s - 6 - 6 * A == 8 * s + 6
assert 41 * s - 6 - 6 * (A + 1) == 8 * s
print(json.dumps(result, indent=2))
