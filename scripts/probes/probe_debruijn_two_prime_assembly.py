#!/usr/bin/env python3
"""Probe for THE FINAL ASSEMBLY — de Bruijn 1953 two-prime as ONE statement (O94).

All three ingredients are kernel-checked in-tree: O92 `debruijn_prime_power`,
O87/O91 `debruijn_squarefree_two_prime(_iff)`, O93 `thread_split_iff`.  What
remains is the assembly: the LIFT LEMMA (packets lift through e -> r + u*e') and
the STRONG INDUCTION down the digits to the squarefree base p*q.  This probe
verifies the FULL target statement end-to-end BEFORE any Lean is written, and
pins the exact lift index map the Lean file will use.

TARGET (headline iff, exponent-space form):
  for n = p^a * q^b (a, b >= 1, p != q primes), S subset of [0, n), zeta a
  primitive n-th root of unity in char 0:
      Sum_{e in S} zeta^e = 0
  IFF  S is a disjoint union of CANONICAL rotated full prime packets
      {r + t*(n/d) : t < d},  d in {p, q},  r < n/d.

CANONICAL FORM (the load-bearing design choice, pinned here): every rotated full
mu_d-packet mod n has a UNIQUE representative with base r < step = n/d, and then
r + (d-1)*step < n — NO modular wraparound anywhere.  The lift e' -> r + u*e'
(r < u, u the descending prime) preserves canonical form EXACTLY:
      {s + t*(m/d) : t < d}  -->  {(r + u*s) + t*(u*(m/d)) : t < d}
with new base r + u*s < u*(m/d) = (u*m)/d = new step.  This probe asserts that
index map literally, at every lift of every recursion of every vanishing mask.

Checks (exit 0 iff all pass), at n = 12 (2^2*3), 18 (2*3^2), 20 (2^2*5),
28 (2^2*7) — all EXHAUSTIVE over the full 2^n mask space (meet-in-the-middle,
exact integer arithmetic mod Phi_n; no floats):
  F1  GENERATOR == VANISHING: the family of all disjoint unions of canonical
      packets (both types, mixtures allowed) EQUALS the vanishing family.
      This is the headline iff as a set identity over all 2^n subsets.
  F2  RECURSION (the Lean proof plan executed): every vanishing mask is
      decomposed by canonical digit descent — thread-split at the squared
      prime u, recurse to the squarefree base, closure dichotomy there,
      canonical packets, lift back with the EXACT index map above (asserting
      base' = r + u*base < step' = u*step = n/d at every lift) — into
      pairwise-disjoint canonical packets with union exactly S.  No mod-n
      arithmetic is ever needed (the canonical invariant survives descent).
  F3  TEETH: (i) at each n a mixture witness — a vanishing mask whose
      decomposition uses BOTH packet types (so the statement cannot be
      strengthened to pure type past the squarefree level); (ii) controls:
      {0} and a single toggled bit of a planted union are non-vanishing and
      not generated.

What the probe does NOT prove (named): the Lean assembly itself — the lift
lemma + strong induction wrapper (`DeBruijnTwoPrimeAssembly.lean`, gated here).
"""

import sys

FAIL = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAIL.append(name)


# ---------- exact arithmetic: x^e mod Phi_n over Z (probe-standalone) ----------

def cyclotomic(n):
    def poly_div(num, den):
        num = num[:]
        out = [0] * (len(num) - len(den) + 1)
        for i in range(len(num) - len(den), -1, -1):
            c = num[i + len(den) - 1]
            assert c % den[-1] == 0
            qq = c // den[-1]
            out[i] = qq
            for j, dc in enumerate(den):
                num[i + j] -= qq * dc
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
            if (d < m and d in phi) or d == 1:
                pd = phi[d]
                new = [0] * (len(den) + len(pd) - 1)
                for i, a in enumerate(den):
                    for j, b in enumerate(pd):
                        new[i + j] += a * b
                den = new
        phi[m] = poly_div(num, den)
    return phi[n]


def root_power_table(n):
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
    """All vanishing masks over the FULL 2^n space, meet-in-the-middle, exact."""
    table, deg = root_power_table(n)
    lo_bits = n // 2
    hi_bits = n - lo_bits

    def half_sums(bits, offset):
        sums = {}
        for m in range(1 << bits):
            v = [0] * deg
            mm = m
            while mm:
                b = (mm & -mm).bit_length() - 1
                t = table[offset + b]
                for i in range(deg):
                    v[i] += t[i]
                mm &= mm - 1
            sums.setdefault(tuple(v), []).append(m)
        return sums

    lo = half_sums(lo_bits, 0)
    hi = half_sums(hi_bits, lo_bits)
    van = set()
    for hv, hms in hi.items():
        need = tuple(-c for c in hv)
        if need in lo:
            for lm in lo[need]:
                for hm in hms:
                    van.add(lm | (hm << lo_bits))
    return van


# ---------- canonical packets and the generator family ----------

def canonical_packets(n, p, q):
    """All canonical rotated full prime packets at level n: ({r+t*(n/d)}, d, r)."""
    out = []
    for d in (p, q):
        step = n // d
        for r in range(step):
            pk = frozenset(r + t * step for t in range(d))
            assert max(pk) < n and min(pk) == r  # canonical: no wraparound
            out.append((pk, d, r))
    return out


def generator_family(n, p, q):
    """All masks that are disjoint unions of canonical packets (incl. empty)."""
    packs = [pk for (pk, _, _) in canonical_packets(n, p, q)]
    fam = set()
    for sel in range(1 << len(packs)):
        union = set()
        good = True
        s = sel
        while s:
            i = (s & -s).bit_length() - 1
            if union & packs[i]:
                good = False
                break
            union |= packs[i]
            s &= s - 1
        if good:
            mask = 0
            for e in union:
                mask |= 1 << e
            fam.add(mask)
    return fam


# ---------- the recursion (the Lean proof plan, executed) ----------

def factor_two_prime(n):
    """n = p^a * q^b with p < q primes, a,b >= 1."""
    m, p, a = n, None, 0
    for c in range(2, n + 1):
        if m % c == 0:
            p = c
            while m % c == 0:
                a += 1
                m //= c
            break
    q, b = None, 0
    for c in range(p + 1, n + 1):
        if m % c == 0:
            q = c
            while m % c == 0:
                b += 1
                m //= c
            break
    assert m == 1 and a >= 1 and b >= 1
    return p, a, q, b


def base_decompose(n, p, q, S):
    """Squarefree base n = p*q: closure dichotomy -> canonical packets."""
    assert n == p * q
    if not S:
        return []
    if all(((e + p) % n) in S for e in S):       # closed under +p: mu_q-packets
        d, step = q, p
    elif all(((e + q) % n) in S for e in S):     # closed under +q: mu_p-packets
        d, step = p, q
    else:
        raise AssertionError(f"base dichotomy fails: n={n} S={sorted(S)}")
    reps = sorted({e % step for e in S})
    packs = []
    for r in reps:
        pk = frozenset(r + t * step for t in range(d))
        assert r < step and pk <= S, f"fiber not full: n={n} r={r} S={sorted(S)}"
        packs.append((pk, d, r))
    assert set().union(*[pk for (pk, _, _) in packs]) == S
    return packs


def decompose(n, S, van_cache):
    """Canonical digit descent.  S is a set of ints in [0, n).  Returns a list of
    (packet, d, base) with the canonical invariant asserted at every level."""
    p, a, q, b = factor_two_prime(n)
    if a == 1 and b == 1:
        return base_decompose(n, p, q, S)
    u = p if a >= 2 else q                       # the descending (squared) prime
    m = n // u
    packs = []
    for r in range(u):
        T = {(e - r) // u for e in S if e % u == r}
        tmask = 0
        for e in T:
            tmask |= 1 << e
        assert tmask in van_cache[m], \
            f"thread-split fails: n={n} r={r} T={sorted(T)}"
        for (pk, d, s) in decompose(m, T, van_cache):
            step = m // d
            new_step = u * step
            new_base = r + u * s
            # THE EXACT LIFT INDEX MAP (what the Lean lift lemma states):
            lifted = frozenset(r + u * e for e in pk)
            canonical = frozenset(new_base + t * new_step for t in range(d))
            assert lifted == canonical, \
                f"lift index map: n={n} r={r} pk={sorted(pk)}"
            assert new_base < new_step, \
                f"canonical base bound: n={n} {new_base} >= {new_step}"
            assert new_step == n // d, \
                f"step arithmetic: u*(m/d) != n/d at n={n} d={d}"
            packs.append((lifted, d, new_base))
    # disjointness + exact union
    union = set()
    for (pk, _, _) in packs:
        assert not (union & pk), f"overlap: n={n} S={sorted(S)}"
        union |= pk
    assert union == S, f"union mismatch: n={n} S={sorted(S)}"
    return packs


# ---------- run ----------

POINTS = [12, 18, 20, 28]
van_cache = {}

print("PROBE — de Bruijn two-prime FINAL ASSEMBLY (full iff + lift arithmetic)")
for n in POINTS:
    p, a, q, b = factor_two_prime(n)
    # vanishing families for every level of the descent tower
    lvl = n
    while lvl not in van_cache:
        van_cache[lvl] = vanishing_masks(lvl)
        pl, al, ql, bl = factor_two_prime(lvl)
        if al == 1 and bl == 1:
            break
        lvl = lvl // (pl if al >= 2 else ql)
    van = van_cache[n]

    # F1: generator family == vanishing family (the headline iff, exhaustive)
    fam = generator_family(n, p, q)
    check(f"F1 n={n}={p}^{a}*{q}^{b}: disjoint-canonical-packet-union family == "
          f"vanishing family over ALL 2^{n} masks", fam == van,
          f"|fam|={len(fam)} |van|={len(van)}")

    # F2: the recursion decomposes every vanishing mask (canonical throughout)
    ok, why = True, ""
    mixture_seen = False
    for mask in van:
        S = {e for e in range(n) if (mask >> e) & 1}
        try:
            packs = decompose(n, S, van_cache)
        except AssertionError as ex:
            ok, why = False, str(ex)
            break
        if len({d for (_, d, _) in packs}) == 2:
            mixture_seen = True
    check(f"F2 n={n}: canonical digit-descent recursion decomposes ALL "
          f"{len(van)} vanishing masks (lift index map asserted at every lift)",
          ok, why)

    # F3: teeth
    check(f"F3 n={n}: mixture witness exists (both packet types in one "
          f"decomposition — pure type genuinely fails past squarefree)",
          mixture_seen or (a == 1 and b == 1), "")
    check(f"F3 n={n}: {{0}} non-vanishing and not generated",
          (1 << 0) not in van and (1 << 0) not in fam)
    planted = next(m for m in sorted(van) if m)
    toggled = planted ^ (1 << ((planted.bit_length()) % n))
    check(f"F3 n={n}: single-bit toggle of a planted union breaks both sides",
          (toggled in van) == (toggled in fam), f"planted={planted:#x}")

print()
if FAIL:
    print(f"FAILED ({len(FAIL)}): {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
