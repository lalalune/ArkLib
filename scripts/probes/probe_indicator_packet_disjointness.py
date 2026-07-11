#!/usr/bin/env python3
"""Probe for de Bruijn step (3): indicator disjointness — issue #232 (O87 candidate).

Setting: n = p^a * q^b two-prime smooth, S a subset of Z_n with vanishing root-of-unity
sum (exact arithmetic in Z[x]/Phi_n, no floats).  The in-tree engine
(CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers) gives mu_q-shift invariant fiber
sums; the candidate Lean brick is:

  SQUAREFREE HEADLINE (n = p*q, a = b = 1): every vanishing indicator subset S is
  closed under e -> e + q  (a disjoint union of rotated full mu_p-packets)
  OR closed under e -> e + p (a disjoint union of rotated full mu_q-packets).
  PURE type — no mixtures exist at the squarefree level.

  Mechanism (what the Lean proof does): with b = 1 ALL fibers A(c), c < q, are equal;
  each fiber set is a subset of [0,p) summing 0/1-weighted powers of a primitive p-th
  root, and the prime dichotomy (equal indicator sums of mu_p => equal sets, or one
  full + one empty) forces: all column sets equal (=> +p closure) or all columns
  empty-or-full (=> +q closure).

Checks (exit 0 iff all pass):
  C1  squarefree n in {6, 10, 15}: EXHAUSTIVE over all 2^n subsets — every vanishing
      subset is +p-closed or +q-closed; both pure types occur (non-vacuity).
  C2  same n: the mechanism itself — per vanishing subset, the CRT column sets are
      all-equal or all in {empty, full}; and all fiber sums are equal.
  C3  NEGATIVE control at prime powers: n = 12, 18 (exhaustive) — vanishing subsets
      violating BOTH coset closures (under + n/p and + n/q) EXIST (mixtures), so the
      squarefree pure-type headline provably does NOT extend verbatim; its honest
      scope is a = b = 1.
  C4  theorem-content control at n = 6: non-vanishing subsets violating both closures
      exist (the vanishing hypothesis is load-bearing).
  C5  n = 12, 18 (exhaustive): every vanishing subset DOES decompose into disjoint
      rotated FULL prime packets (mixed types allowed) — the O67 numerical statement
      re-verified by a partition DFS (the still-open full de Bruijn target).
  C6  recursion seed at prime powers: for n = 12 (grid 4x3) and n = 18 (grid 9x2),
      for every vanishing subset, every pair of CRT column indicator differences is
      divisible by Phi_{p^a} as a polynomial (the Z-combination-of-rotated-packets
      form) — the correct a >= 2 generalization of the dichotomy (which itself fails
      for a >= 2: equal sums no longer force equal-or-full/empty sets; we count the
      violations of the naive dichotomy to document this).

n = 36 is named as infeasible for exhaustive enumeration (2^36); not sampled here —
the prime-power negative/positive structure is already decided at 12 and 18.
"""

import sys
from math import gcd

# ---------- exact polynomial helpers (integer coefficients, ascending) ----------

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r

def polydivmod(num, den):
    # den monic (leading coeff 1); exact integer division
    num = num[:]
    dn = len(den) - 1
    assert den[-1] == 1
    q = [0] * (max(len(num) - dn, 1))
    for i in range(len(num) - 1, dn - 1, -1):
        c = num[i]
        if c:
            q[i - dn] = c
            for j in range(dn + 1):
                num[i - dn + j] -= c * den[j]
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    return q, num

_cyc_cache = {}

def cyclotomic(n):
    if n in _cyc_cache:
        return _cyc_cache[n]
    num = [-1] + [0] * (n - 1) + [1]  # x^n - 1
    den = [1]
    for d in range(1, n):
        if n % d == 0:
            den = polymul(den, cyclotomic(d))
    q, r = polydivmod(num, den)
    assert all(c == 0 for c in r), f"Phi_{n} division not exact"
    _cyc_cache[n] = q
    return q

def power_residues(n):
    """r_e = x^e mod Phi_n for e < n, as tuples of length deg Phi_n."""
    phi = cyclotomic(n)
    m = len(phi) - 1
    res = []
    cur = [0] * m
    cur[0] = 1
    res.append(tuple(cur))
    for _ in range(1, n):
        nxt = [0] * m
        top = cur[m - 1]
        for i in range(m - 1):
            nxt[i + 1] = cur[i]
        if top:
            for i in range(m):
                nxt[i] -= top * phi[i]
        nxt[0] += 0
        cur = nxt
        res.append(tuple(cur))
    return res

def prime_factors(n):
    fs, d = [], 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs

def vanishing_subsets(n):
    """Exhaustive: bitmasks of subsets of Z_n with vanishing sum of zeta^e."""
    res = power_residues(n)
    m = len(res[0])
    out = []
    for mask in range(1 << n):
        acc = [0] * m
        mm = mask
        e = 0
        while mm:
            if mm & 1:
                r = res[e]
                for i in range(m):
                    acc[i] += r[i]
            mm >>= 1
            e += 1
        if all(c == 0 for c in acc):
            out.append(mask)
    return out

def closed_under(mask, t, n):
    S = [e for e in range(n) if (mask >> e) & 1]
    return all((mask >> ((e + t) % n)) & 1 for e in S)

def decompose_disjoint_packets(mask, n, primes):
    """DFS: partition the subset into full rotated prime packets {e + k*(n/p)}."""
    if mask == 0:
        return True
    e = (mask & -mask).bit_length() - 1
    for p in primes:
        step = n // p
        coset = 0
        for k in range(p):
            coset |= 1 << ((e + k * step) % n)
        if coset & mask == coset:
            if decompose_disjoint_packets(mask & ~coset, n, primes):
                return True
    return False

def grid_columns(mask, n, N, M):
    """CRT grid (N x M), gridMap(j,c) = (j*M + c*N) % n. Column sets col[c] subset [0,N)."""
    cols = []
    for c in range(M):
        col = frozenset(j for j in range(N) if (mask >> ((j * M + c * N) % n)) & 1)
        cols.append(col)
    return cols

def col_sum_vec(col, N, n, res_pow):
    """Fiber sum  sum_{j in col} xi^j  with xi = zeta^M: vector in Z[x]/Phi_n."""
    m = len(res_pow[0])
    acc = [0] * m
    for j in col:
        r = res_pow[j]
        for i in range(m):
            acc[i] += r[i]
    return tuple(acc)

def diff_divisible_by_packet(colX, colY, Pa, pp):
    """Is 1_X - 1_Y on [0,Pa) divisible by Phi_{p^a}?  Phi_{p^a} = sum_t x^{t*Pa/pp};
    equivalent: d = Phi * R, deg R < Pa/pp  <=>  slices of d by step Pa/pp all equal."""
    Q = Pa // pp  # p^{a-1}
    d = [(1 if j in colX else 0) - (1 if j in colY else 0) for j in range(Pa)]
    # d divisible by Phi_{p^a} (= packet in x^Q of length pp) iff polynomial division
    # exact; for deg d < Pa this is equivalent to d = G*R with deg R < Q, i.e. all pp
    # slices d[i*Q + s] equal as i varies -- NO, that is the statement for multiples.
    # Do the honest division check.
    phi = [0] * (Q * (pp - 1) + 1)
    for t in range(pp):
        phi[t * Q] = 1
    num = d[:]
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    if num == [0]:
        return True
    if len(num) - 1 < len(phi) - 1:
        return False
    q, r = polydivmod(num, phi)
    return all(c == 0 for c in r)

def main():
    ok = True

    def check(cond, label):
        nonlocal ok
        print(("PASS" if cond else "FAIL"), label)
        if not cond:
            ok = False

    # ---------------- C1 + C2: squarefree exhaustive ----------------
    for n in (6, 10, 15):
        p, q = prime_factors(n)
        van = vanishing_subsets(n)
        # C1: pure-type closure
        viol1 = []
        only_p = only_q = both = 0
        for mask in van:
            cp = closed_under(mask, q, n)   # +q closure <=> union of mu_p-cosets
            cq = closed_under(mask, p, n)   # +p closure <=> union of mu_q-cosets
            if not (cp or cq):
                viol1.append(mask)
            elif cp and cq:
                both += 1
            elif cp:
                only_p += 1
            else:
                only_q += 1
        check(not viol1,
              f"C1 n={n} (p={p},q={q}): all {len(van)} vanishing subsets +{q}- or "
              f"+{p}-closed (mu_p-only {only_p}, mu_q-only {only_q}, both {both})")
        check(only_p > 0 and only_q > 0, f"C1 n={n}: both pure types occur")

        # C2: the mechanism — columns all-equal or all empty/full; fibers all equal
        res_pow_xi = power_residues(n)  # xi = zeta^q has exponents j*q
        viol2 = 0
        for mask in van:
            cols = grid_columns(mask, n, p, q)  # N=p, M=q
            alleq = all(c == cols[0] for c in cols)
            ef = all(len(c) in (0, p) for c in cols)
            if not (alleq or ef):
                viol2 += 1
            # fiber sums equal (xi^j = zeta^(j*q))
            vecs = set()
            for col in cols:
                vecs.add(col_sum_vec(frozenset((j * q) % n for j in col), p, n,
                                     res_pow_xi))
            if len(vecs) > 1:
                viol2 += 1
        check(viol2 == 0, f"C2 n={n}: column dichotomy + equal fibers ({len(van)} subsets)")

    # ---------------- C3 + C5 + C6: prime-power exhaustive ----------------
    for n, (Pa, M) in ((12, (4, 3)), (18, (9, 2))):
        primes = prime_factors(n)
        p, q = primes
        van = vanishing_subsets(n)
        # C3: pure-type closure FAILS at prime powers (mixtures exist)
        mix = [mask for mask in van
               if not closed_under(mask, n // p, n) and not closed_under(mask, n // q, n)]
        check(len(mix) > 0,
              f"C3 n={n}: pure-type closure violated by {len(mix)}/{len(van)} vanishing "
              f"subsets (squarefree headline does NOT extend; e.g. mask {mix[0] if mix else None:#x})")
        # C5: disjoint full-packet decomposition (mixed) — the open de Bruijn target
        bad5 = [mask for mask in van if not decompose_disjoint_packets(mask, n, primes)]
        check(not bad5,
              f"C5 n={n}: all {len(van)} vanishing subsets decompose into disjoint "
              f"rotated full prime packets")
        # C6: recursion seed — column differences divisible by Phi_{p^a};
        #     also count naive-dichotomy violations at the composite side
        pp = prime_factors(Pa)[0]
        res_pow_xi = power_residues(n)
        bad6 = 0
        naive_viol = 0
        for mask in van:
            cols = grid_columns(mask, n, Pa, M)
            for i in range(M):
                for j in range(i + 1, M):
                    if not diff_divisible_by_packet(cols[i], cols[j], Pa, pp):
                        bad6 += 1
                    if cols[i] != cols[j] and not (
                            len(cols[i]) in (0, Pa) and len(cols[j]) in (0, Pa)):
                        naive_viol += 1
        check(bad6 == 0,
              f"C6 n={n} (grid {Pa}x{M}): all column pair differences divisible by "
              f"Phi_{Pa} ({len(van)} subsets); naive dichotomy violated {naive_viol} "
              f"times (a>=2 needs the packet-combination form)")

    # ---------------- C4: vanishing hypothesis load-bearing ----------------
    n = 6
    res = power_residues(n)
    m = len(res[0])
    nonvan_viol = 0
    for mask in range(1, 1 << n):
        acc = [0] * m
        for e in range(n):
            if (mask >> e) & 1:
                for i in range(m):
                    acc[i] += res[e][i]
        if any(acc):
            if not closed_under(mask, 3, n) and not closed_under(mask, 2, n):
                nonvan_viol += 1
    check(nonvan_viol > 0,
          f"C4 n=6: {nonvan_viol} NON-vanishing subsets violate both closures "
          f"(hypothesis load-bearing)")

    print("OVERALL:", "PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
