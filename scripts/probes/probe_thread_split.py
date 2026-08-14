#!/usr/bin/env python3
"""Probe for the THREAD-SPLIT brick — issue #232 (O93 candidate).

O92 pinned the single remaining wall for de Bruijn 1953 two-prime as THREAD-SPLIT:
for p^2 | n and a primitive n-th root zeta (char 0), a vanishing indicator sum
Sum_{e in S} zeta^e = 0 splits thread-by-thread — writing e = r + p*e' (r < p),
every thread sum Sum_{e' in T_r} (zeta^p)^{e'} vanishes at level n/p, and
conversely (trivial linearity).  O92's probe verified the iff exhaustively at
n = 12, 18 only.  This probe extends the measurement to the brief's points
n = 20, 28, 50 (p^2 | n with a second prime present) plus a bonus odd-p^2 point
n = 45, BEFORE the Lean statement.

Exact integer arithmetic throughout (reduction mod Phi_n over Z; no floats).

Checks (exit 0 iff all pass):
  T1 n=20 = 2^2*5  (p=2, m=10): EXHAUSTIVE over all 2^20 masks.  The vanishing
     family (meet-in-the-middle, exact) must EQUAL the thread-product family
     {masks whose 2 threads both vanish at level 10} — since thread decomposition
     is a bijection masks <-> (thread-tuple)s, set equality IS the exhaustive iff.
     Count cross-check: |van(20)| == |van(10)|^2.
  T2 n=28 = 2^2*7  (p=2, m=14): same, EXHAUSTIVE over all 2^28 masks via the same
     set identity (meet-in-the-middle at 28; product family from van(14)^2).
  T3 n=50 = 2*5^2  (p=5, m=10): SAMPLED.  (i) 2000 planted thread-tuples from
     van(10)^5 — composed mask must vanish at 50 (converse direction);
     (ii) 20000 random masks — iff must hold pointwise (vanish(50) == all 5
     threads in van(10)); (iii) 2000 adversarial single-bit toggles of planted
     vanishing masks — must NOT vanish AND must have a bad thread (teeth: the
     iff discriminates).
  T4 n=45 = 3^2*5  (p=3, m=15): SAMPLED, same three sub-checks (odd p).
  T5 controls: at n = 20 and 28, a mask with exactly one bad thread is
     non-vanishing (one-sided failure is impossible — both sides flip together).

What the probe does NOT prove (named): the thread-split lemma itself — the
Q(zeta_{n/p})-linear independence of 1, zeta, ..., zeta^{p-1}, i.e.
minpoly Q(zeta^p) zeta = X^p - zeta^p.  That is the Lean brick this probe gates
(`ThreadSplit.lean`).
"""

import random
import sys

random.seed(232)
FAIL = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAIL.append(name)


# ---------- exact arithmetic: indicator polynomial mod Phi_n over Z ----------
# (same machinery as probe_prime_power_descent.py; standalone by probe convention)

def cyclotomic(n):
    """Phi_n as int coefficient list (exact, via repeated division of x^n - 1)."""
    def poly_div(num, den):
        num = num[:]
        out = [0] * (len(num) - len(den) + 1)
        for i in range(len(num) - len(den), -1, -1):
            c = num[i + len(den) - 1]
            assert c % den[-1] == 0
            q = c // den[-1]
            out[i] = q
            for j, dc in enumerate(den):
                num[i + j] -= q * dc
        assert all(c == 0 for c in num), "non-exact division"
        return out

    def divisors(m):
        return [d for d in range(1, m + 1) if m % d == 0]

    phi = {1: [-1, 1]}
    for m in sorted(divisors(n)):
        if m == 1 or m in phi:
            continue
        num = [0] * (m + 1)
        num[0], num[m] = -1, 1
        den = [1]
        for d in divisors(m):
            if d < m and d in phi or d == 1:
                pd = phi[d]
                new = [0] * (len(den) + len(pd) - 1)
                for i, a in enumerate(den):
                    for j, b in enumerate(pd):
                        new[i + j] += a * b
                den = new
        phi[m] = poly_div(num, den)
    return phi[n]


def root_power_table(n):
    """x^e mod Phi_n for e < n, as tuples of length deg Phi_n (exact ints)."""
    phi = cyclotomic(n)
    deg = len(phi) - 1
    assert phi[-1] == 1
    table = []
    cur = [0] * deg
    if deg > 0:
        cur[0] = 1
    table.append(tuple(cur))
    for _ in range(1, n):
        nxt = [0] * (deg + 1)
        for i, c in enumerate(cur):
            nxt[i + 1] = c
        if nxt[deg] != 0:
            t = nxt[deg]
            for i in range(deg):
                nxt[i] -= t * phi[i]
            nxt[deg] = 0
        cur = nxt[:deg]
        table.append(tuple(cur))
    return table, deg


def vanishing_masks(n):
    """All masks (subsets of Z_n) with vanishing root-of-unity sum, exact
    (meet-in-the-middle over the full 2^n space)."""
    table, deg = root_power_table(n)
    out = set()
    half = n // 2
    lows = {}
    for lo in range(1 << half):
        v = [0] * deg
        m = lo
        e = 0
        while m:
            if m & 1:
                row = table[e]
                for i in range(deg):
                    v[i] += row[i]
            m >>= 1
            e += 1
        lows.setdefault(tuple(v), []).append(lo)
    for hi in range(1 << (n - half)):
        v = [0] * deg
        m = hi
        e = half
        while m:
            if m & 1:
                row = table[e]
                for i in range(deg):
                    v[i] += row[i]
            m >>= 1
            e += 1
        key = tuple(-c for c in v)
        for lo in lows.get(key, []):
            out.add((hi << half) | lo)
    return out


def mask_vanishes(n, mask, table, deg):
    v = [0] * deg
    e = 0
    m = mask
    while m:
        if m & 1:
            row = table[e]
            for i in range(deg):
                v[i] += row[i]
        m >>= 1
        e += 1
    return all(c == 0 for c in v)


# ---------- thread plumbing ----------

def threads_of(n, p, mask):
    """The p thread masks at level m = n // p: T_r = {e' : r + p*e' in S}."""
    m = n // p
    out = [0] * p
    for e in range(n):
        if (mask >> e) & 1:
            out[e % p] |= 1 << (e // p)
    assert all(t < (1 << m) for t in out)
    return out


def compose(n, p, threads):
    """Inverse of threads_of: mask with bit r + p*e' iff bit e' of threads[r]."""
    m = n // p
    mask = 0
    for r in range(p):
        for e in range(m):
            if (threads[r] >> e) & 1:
                mask |= 1 << (r + p * e)
    return mask


# ---------- T1 / T2: exhaustive set identities at n = 20, 28 ----------

print("T1/T2 — exhaustive thread-split iff at n = 20, 28 (p = 2)")
for n in (20, 28):
    p = 2
    m = n // p
    van_m = vanishing_masks(m)
    van_n = vanishing_masks(n)
    product = {compose(n, p, (t0, t1)) for t0 in van_m for t1 in van_m}
    check(f"T n={n}: vanishing family == thread-product family "
          f"(EXHAUSTIVE iff over all 2^{n} masks)", van_n == product,
          f"|van({n})|={len(van_n)} |van({m})|^2={len(van_m) ** 2}")
    check(f"T n={n}: |van({n})| == |van({m})|^2",
          len(van_n) == len(van_m) ** 2)
    # T5 control: exactly one bad thread -> non-vanishing (teeth)
    good = next(t for t in van_m if t)          # a nonempty vanishing thread
    bad = next(t for t in range(1, 1 << m) if t not in van_m)
    one_bad = compose(n, p, (good, bad))
    check(f"T5 n={n}: mask with exactly one bad thread does NOT vanish",
          one_bad not in van_n)

# ---------- T3 / T4: sampled at n = 50 (p=5), n = 45 (p=3) ----------

for (n, p) in ((50, 5), (45, 3)):
    m = n // p
    print(f"T — sampled thread-split iff at n = {n} (p = {p}, m = {m})")
    van_m = sorted(vanishing_masks(m))
    table, deg = root_power_table(n)
    table_m, deg_m = root_power_table(m)
    van_m_set = set(van_m)

    # (i) planted: composed vanishing threads must vanish at n
    ok = True
    planted = []
    for _ in range(2000):
        ths = tuple(random.choice(van_m) for _ in range(p))
        mask = compose(n, p, ths)
        planted.append(mask)
        if not mask_vanishes(n, mask, table, deg):
            ok = False
            break
    check(f"T n={n}: 2000 planted all-threads-vanishing masks all vanish", ok)

    # (ii) random: pointwise iff
    ok = True
    n_vanish = 0
    for _ in range(20000):
        mask = random.getrandbits(n)
        lhs = mask_vanishes(n, mask, table, deg)
        rhs = all(t in van_m_set for t in threads_of(n, p, mask))
        if lhs != rhs:
            ok = False
            break
        if lhs:
            n_vanish += 1
    check(f"T n={n}: 20000 random masks, iff holds pointwise", ok,
          f"({n_vanish} vanished)")

    # (iii) adversarial toggles of planted vanishing masks (teeth)
    ok = True
    for mask in planted[:2000]:
        e = random.randrange(n)
        toggled = mask ^ (1 << e)
        if mask_vanishes(n, toggled, table, deg):
            ok = False
            break
        ths = threads_of(n, p, toggled)
        if all(t in van_m_set for t in ths):
            ok = False
            break
        # the toggled thread is exactly the bad one
        if ths[e % p] in van_m_set:
            ok = False
            break
    check(f"T n={n}: 2000 single-bit toggles of planted masks: "
          f"non-vanishing AND the toggled thread is the bad thread", ok)

print()
if FAIL:
    print(f"FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASS")
sys.exit(0)
