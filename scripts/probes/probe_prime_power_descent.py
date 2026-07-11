#!/usr/bin/env python3
"""Probe for the de Bruijn WIRING pass — issue #232 (O92 candidate).

O90 proved the descent engine (packet divisibility at digit a <-> p-fold slice
replication at a-1, both directions, any integral domain).  Its closing words name
the remainder as WIRING: run the recursion down the digits + assemble mixed disjoint
packets at composite levels, with the O67-verified mixed-decomposition census as the
target shape.  This probe measures that wiring shape BEFORE any Lean statement.

Two layers, falsify-first (exit 0 iff all checks pass):

LAYER A — the SINGLE-PRIME-POWER law (the Lean brick's exact statement):
  for n = p^(a+1), a vanishing 0/1 indicator sum of mu_n is EQUIVALENT to closure of
  the exponent set under e |-> e + p^a, i.e. S is a disjoint union of rotated full
  mu_p-packets {s + t*p^a : t < p}.  Mechanism (the one-shot O90 application, no
  recursion needed at a pure prime power): vanishing <=> Phi_{p^(a+1)} | indicator
  polynomial (deg < p^(a+1)) <=> p-fold slice replication of the coefficients.
  A1  exhaustive at n = 4, 8, 9, 16 (all 2^n subsets): vanishing <=> +p^a-closed;
      count of vanishing subsets = 2^(p^a) exactly.
  A2  sampled at n = 27, 25 (20000 random masks + all closed sets): same iff.
  A3  control (hypothesis load-bearing): at each exhaustive n there exist non-closed
      subsets, and every one of them has NON-vanishing sum.

LAYER B — the TWO-PRIME digit-descent recursion at n = 12 (4*3) and n = 18 (2*9):
  B1  exhaustive vanishing census (exact arithmetic mod Phi_n over Z): counts must be
      100 (n=12) and 1000 (n=18) — O87's exhaustive numbers; nonempty counts 99/999
      (O67); mixture counts (vanishing, nonempty, violating BOTH global coset
      closures) must be 24 (n=12) and 432 (n=18) — O87's measured scope boundary.
  B2  the RECURSION: decompose every vanishing subset by digit descent —
      thread-split at the squared prime p (e = r + p*e', threads T_r at level n/p;
      EMPIRICAL CHECK of the thread-split lemma: every thread of a vanishing subset
      is itself vanishing at level n/p), recurse to the squarefree base n = 6, apply
      the O87 pure-type dichotomy there, lift packets back (x |-> r + p*x).  Verify
      for EVERY vanishing subset: the produced packets are genuine rotated full
      mu_p/mu_q-packets at level n, pairwise disjoint, with union exactly S.
  B3  thread-split is an IFF (the wall lemma's exact shape, both directions):
      a subset of Z_n vanishes IFF all p thread-projections vanish at level n/p —
      verified EXHAUSTIVELY against the direct census (independent second witness:
      the census of B1 must equal the product structure of B3).
  B4  independent third witness: generate ALL disjoint unions of rotated full
      mu_p/mu_q-packets directly (2^10 families at 12, 2^15 at 18, filtered to
      pairwise disjoint) — the resulting family of subsets must EQUAL the vanishing
      family (de Bruijn's N-combination statement for indicators, as a set identity).
  B5  control: a specific non-vanishing subset ({0}) is produced by NO generator
      family and has a non-vanishing thread.

What the probe does NOT prove (named): the thread-split lemma itself
(Q(zeta_{n/p})-linear independence of 1, zeta, ..., zeta^{p-1} when p^2 | n) has no
in-tree Lean brick; it is the named wall for the full two-prime assembly.
"""

import itertools
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

def cyclotomic(n):
    """Phi_n as int coefficient list (exact, via repeated division of x^n - 1)."""
    # poly as dict/list ops over Z; compute via divisors
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
                # multiply den by phi[d]
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
    """All masks (subsets of Z_n) with vanishing root-of-unity sum, exact."""
    table, deg = root_power_table(n)
    out = set()
    # meet in the middle for speed
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


def mask_vanishes(n, mask, table=None, deg=None):
    if table is None:
        table, deg = root_power_table(n)
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


def closed_under(n, mask, shift):
    s = {e for e in range(n) if (mask >> e) & 1}
    return all(((e + shift) % n) in s for e in s)


# ---------- LAYER A: single prime power ----------

print("LAYER A — single-prime-power law: vanishing <=> closed under +p^a")
for (p, apow) in [(2, 4), (2, 8), (3, 9), (2, 16)]:
    n = apow
    q = n // p
    table, deg = root_power_table(n)
    van = vanishing_masks(n)
    closed = {m for m in range(1 << n) if closed_under(n, m, q)}
    check(f"A1 n={n}: vanishing == closed(+{q})", van == closed,
          f"|vanishing|={len(van)} |closed|={len(closed)}")
    check(f"A1 n={n}: count == 2^{q}", len(van) == 2 ** q)
    nonclosed_sample = [m for m in list(range(1, 1 << n))[:2000] if m not in closed]
    check(f"A3 n={n}: non-closed subsets exist and none vanish",
          len(nonclosed_sample) > 0 and all(m not in van for m in nonclosed_sample))

for (p, n) in [(3, 27), (5, 25)]:
    q = n // p
    table, deg = root_power_table(n)
    ok = True
    # all closed sets vanish (closed sets = unions of q cosets {s,s+q,...})
    for _ in range(2000):
        cos = random.getrandbits(q)
        mask = 0
        for s in range(q):
            if (cos >> s) & 1:
                for t in range(p):
                    mask |= 1 << (s + t * q)
        if not mask_vanishes(n, mask, table, deg):
            ok = False
            break
    check(f"A2 n={n}: 2000 random +{q}-closed sets all vanish", ok)
    ok = True
    cnt_nc = 0
    for _ in range(20000):
        mask = random.getrandbits(n)
        if not closed_under(n, mask, q):
            cnt_nc += 1
            if mask_vanishes(n, mask, table, deg):
                ok = False
                break
    check(f"A2 n={n}: {cnt_nc} random non-closed sets all NON-vanishing", ok)

# ---------- LAYER B: two-prime digit descent at 12, 18 ----------

print("LAYER B — two-prime digit-descent recursion at n = 12, 18")

VAN6 = vanishing_masks(6)


def decompose(n, mask):
    """Digit-descent decomposer.  Returns list of (d, frozenset packet) with d the
    prime type, or raises AssertionError.  n in {6, 12, 18}."""
    if mask == 0:
        return []
    if n == 6:
        s = frozenset(e for e in range(6) if (mask >> e) & 1)
        if closed_under(6, mask, 2):  # union of {r, r+2, r+4} = mu_3-packets
            reps = sorted({min(r, (r + 2) % 6, (r + 4) % 6) for r in s})
            packs = [(3, frozenset((r + 2 * t) % 6 for t in range(3))) for r in reps]
        elif closed_under(6, mask, 3):  # union of {r, r+3} = mu_2-packets
            reps = sorted({min(r, (r + 3) % 6) for r in s})
            packs = [(2, frozenset((r + 3 * t) % 6 for t in range(2))) for r in reps]
        else:
            raise AssertionError(f"base dichotomy fails at n=6 mask={mask:#x}")
        return packs
    # thread-split at the squared prime
    p = 2 if n == 12 else 3
    npr = n // p
    packets = []
    for r in range(p):
        tmask = 0
        for e in range(n):
            if (mask >> e) & 1 and e % p == r:
                tmask |= 1 << ((e - r) // p)
        # EMPIRICAL thread-split check: thread must vanish at level n/p
        assert tmask in VAN6, \
            f"thread-split FAILS: n={n} mask={mask:#x} thread r={r} non-vanishing"
        for (d, pk) in decompose(npr, tmask):
            lifted = frozenset((r + p * x) % n for x in pk)
            # lifted packet must be a genuine rotated full mu_d-packet at level n
            s0 = min(lifted)
            genuine = frozenset((s0 + t * (n // d)) % n for t in range(d))
            assert lifted == genuine, \
                f"lift not a packet: n={n} mask={mask:#x} {sorted(lifted)}"
            packets.append((d, lifted))
    return packets


def all_packets(n):
    """All rotated full mu_p-packets at level n = p^a*q^b for its two primes."""
    out = []
    for d in (2, 3):
        for s in range(n // d):
            out.append((d, frozenset((s + t * (n // d)) % n for t in range(d))))
    return out


for n in [12, 18]:
    p = 2 if n == 12 else 3        # the squared prime (thread-split prime)
    van = vanishing_masks(n)
    nonempty = [m for m in van if m]
    expect_total = 100 if n == 12 else 1000
    expect_mix = 24 if n == 12 else 432
    check(f"B1 n={n}: |vanishing| == {expect_total} (O87 exhaustive census)",
          len(van) == expect_total, f"got {len(van)}")
    check(f"B1 n={n}: nonempty == {expect_total - 1} (O67 census)",
          len(nonempty) == expect_total - 1)
    mixtures = [m for m in nonempty
                if not closed_under(n, m, n // 2) and not closed_under(n, m, n // 3)]
    check(f"B1 n={n}: mixtures (violate both closures) == {expect_mix} (O87)",
          len(mixtures) == expect_mix, f"got {len(mixtures)}")

    # B2: recursion decomposes every vanishing subset into disjoint packets
    ok = True
    why = ""
    for m in van:
        try:
            packs = decompose(n, m)
        except AssertionError as e:
            ok, why = False, str(e)
            break
        union = set()
        disjoint = True
        for (_, pk) in packs:
            if union & pk:
                disjoint = False
            union |= pk
        target = {e for e in range(n) if (m >> e) & 1}
        if not (disjoint and union == target):
            ok, why = False, f"partition mismatch mask={m:#x}"
            break
    check(f"B2 n={n}: digit-descent recursion decomposes ALL {len(van)} "
          f"vanishing subsets into disjoint genuine packets", ok, why)

    # B3: thread-split iff, exhaustively: vanish(mask) <=> all threads in VAN6
    def threads_vanish(mask):
        for r in range(p):
            tmask = 0
            for e in range(n):
                if (mask >> e) & 1 and e % p == r:
                    tmask |= 1 << ((e - r) // p)
            if tmask not in VAN6:
                return False
        return True
    product_family = {m for m in range(1 << n) if threads_vanish(m)}
    check(f"B3 n={n}: thread-split IFF exhaustive over all 2^{n} masks "
          f"(vanish <=> all {p} threads vanish at n/{p})", product_family == van)

    # B4: independent generator — all disjoint unions of packets == vanishing family
    packs = all_packets(n)
    fam = set()
    for sel in range(1 << len(packs)):
        chosen = [packs[i][1] for i in range(len(packs)) if (sel >> i) & 1]
        union = set()
        good = True
        for pk in chosen:
            if union & pk:
                good = False
                break
            union |= pk
        if good:
            mask = 0
            for e in union:
                mask |= 1 << e
            fam.add(mask)
    check(f"B4 n={n}: disjoint-packet-union family == vanishing family "
          f"(de Bruijn N-combination, set identity)", fam == van,
          f"|fam|={len(fam)} |van|={len(van)}")

    # B5: control
    check(f"B5 n={n}: {{0}} non-vanishing, not generated, has bad thread",
          (1 not in van) and (1 not in fam) and not threads_vanish(1))

print()
if FAIL:
    print(f"FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASS")
sys.exit(0)
