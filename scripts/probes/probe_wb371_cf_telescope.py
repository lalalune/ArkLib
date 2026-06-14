#!/usr/bin/env python3
"""
CF-telescope probe: slack-2 chain anatomy at (31,10,4) (D_def = 2, k=1).

Questions:
 (1) What core sizes appear among graded witnesses sharing structure?
     (slack-2 allows |T| in {w-2, w-1, w} with deg g <= D_def - (w-|T|).)
 (2) For two witnesses sharing a (w-1)-core K with full size: does the
     factorization g_i = a*(X-tau_i)*(linear_i) hold, and what is the shared
     structure?  For (w-2)-cores: g_i = a*prod of two (X-tau)'s?
 (3) The telescope: does the exact identity Phi*m_K = (residual g)*m_D hold
     after cancelling the (X-t) factors of the witness's extra points?
Method: enumerate graded fiber members for adversarial (l0, u) with engineered
cores of size w-1 and w-2; solve the FULL linear system per witness (gamma, p,
g coefficients) as in the two-sided probe to get actual witness data for a
synthetic stack; check factorizations exactly.
Simplification: work at the fiber level (mod-l0 only) for structure (1)-(2);
the full-system check (3) on the two-sided solutions of random stacks.
"""
import itertools, random

q, n, w = 31, 10, 4
D_def = 3 * w - n  # 2

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

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % q, 1])
    return out

def polinv_mod(u, l0):
    def deg(p):
        d = -1
        for i in range(len(p)):
            if p[i] % q:
                d = i
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

def poldiv_exact(a, b):
    """return a / b if exact else None"""
    a = [x % q for x in a]
    db = max(i for i in range(len(b)) if b[i] % q)
    inv = pow(b[db], q - 2, q)
    quot = [0] * max(1, len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % q
        if c:
            f = (c * inv) % q
            quot[i - db] = f
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % q
    if any(x % q for x in a[:db]):
        return None
    return quot

random.seed(71)
pool = []
while len(pool) < 30:
    l0 = [random.randrange(q) for _ in range(w)] + [1]
    if all(poleval(l0, x) for x in D):
        pool.append(l0)

print(f"(q,n,w)=({q},{n},{w}), D_def={D_def}, D={D}")

# Engineer a (w-2)-core: pick K2 (size 2), set u := m_K2 (then m_K2*u^{-1} = 1
# constant: members T = K2 ∪ {a,b} have m_T*u^{-1} = (X-a)(X-b): deg 2 <= D_def ✓
# ALL C(n-2, 2) pairs are members! And (w-1)-cores K1 ⊃ K2 give chains too.)
for trial in range(3):
    l0 = random.choice(pool)
    K2 = sorted(random.sample(D, 2))
    u = m_of(K2)
    uinv = polinv_mod(u, l0)
    if uinv is None:
        continue
    members = []
    for j in range(D_def + 1):
        size = w - j
        budget = D_def - j
        for T in itertools.combinations(D, size):
            rep = polmod(polmul(m_of(T), uinv), l0)
            dr = max((i for i in range(len(rep)) if rep[i] % q), default=-1)
            if dr == -1:
                continue
            if dr <= budget:
                members.append((T, dr, tuple(rep[:dr + 1])))
    n_with_K2 = sum(1 for T, _, _ in members if set(K2) <= set(T))
    n_without = len(members) - n_with_K2
    print(f"\n  l0={l0} K2={K2}: members={len(members)} "
          f"(containing K2: {n_with_K2}, exotic: {n_without})")
    # factorization check: for members T ⊇ K2 of full size: is the g-class
    # rep == c * prod_{t in T\K2} (X - t)?
    ok = 0; bad = 0
    for T, dr, rep in members:
        if set(K2) <= set(T) and len(T) == w:
            extra = sorted(set(T) - set(K2))
            pred = m_of(extra)  # monic (X-t1)(X-t2)
            # rep should be proportional to pred
            quot = None
            # check proportionality: rep == c*pred for some c
            cvals = set()
            consistent = True
            for i in range(max(len(rep), len(pred))):
                r = rep[i] if i < len(rep) else 0
                p_ = pred[i] if i < len(pred) else 0
                if p_ == 0:
                    if r % q:
                        consistent = False
                        break
                else:
                    cvals.add((r * pow(p_, q - 2, q)) % q)
            if consistent and len(cvals) == 1:
                ok += 1
            else:
                bad += 1
    print(f"    factorization g = c*m_(T\\K2): holds {ok}, fails {bad}")
    # multi-level: (w-1)-cores inside: for K1 = K2 ∪ {x}: members containing K1
    levels = {}
    for x in D:
        if x in K2:
            continue
        K1 = sorted(K2 + [x])
        cnt = sum(1 for T, _, _ in members if set(K1) <= set(T))
        if cnt:
            levels[tuple(K1)] = cnt
    print(f"    (w-1)-subcore member counts: {sorted(levels.values(), reverse=True)[:6]}")
