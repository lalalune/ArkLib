#!/usr/bin/env python3
"""Probe for the packet-combination divisibility brick — issue #232 (O90 candidate).

O87 measured (probe_indicator_packet_disjointness.py, C6): at prime powers, every CRT
column indicator difference of a vanishing subset is divisible by Phi_{p^a} (100% at
n = 12, 18), while the naive squarefree dichotomy fails there.  The named next brick
is the PACKET-COMBINATION form:

  a polynomial d with coefficients in {-1,0,1} (an indicator difference), divisible by
  Phi_{p^a} = Sum_{t<p} X^(t*p^(a-1)), with deg d < p^a, has quotient R of
  deg R < p^(a-1) = Q, and moreover R is read off the BOTTOM SLICE of d
  (R[s] = d[s] for s < Q) — so d IS the bounded-coefficient combination
  d = Sum_{s<Q} d[s] * X^s * Phi_{p^a} of rotated packets, with combination
  coefficients literally coefficients of d, hence in {-1,0,1}.

This probe measures the exact coefficient structure BEFORE the Lean proof (the brief's
demand: which quotients occur for real indicator differences at n = 12, 18 — are the
quotient coefficients also in a bounded set?), and runs the controls that show every
hypothesis is load-bearing.

Checks (exit 0 iff all pass):
  Q1  n = 12 (grid 4x3, p=2, a=2, Q=2) and n = 18 (grid 9x2, p=3, a=2, Q=3),
      EXHAUSTIVE over all vanishing subsets, every ordered CRT column pair:
      d = 1_X - 1_Y is divisible by Phi_{p^a} (re-verifies O87 C6) AND
      (i) the honest-division quotient R has deg R < Q,
      (ii) all coefficients of R lie in {-1,0,1},
      (iii) R[s] = d[s] for s < Q (the bottom-slice identity),
      (iv) the rotated-packet combination reconstructs: d = Sum_{s<Q} d[s]*X^s*Phi.
  Q2  NEGATIVE control (the degree hypothesis is load-bearing): d = Phi * X^Q has
      coefficients in {0,1} and is divisible, but deg d = p^a (not < p^a); its
      quotient has deg = Q (NOT < Q) and the rotated-packet RECONSTRUCTION with
      shifts < Q fails.  (Finding: the bottom-slice identity R[s] = d[s], s < Q,
      holds for ANY quotient — convolution from higher slices never reaches down —
      it is the degree bound that makes the bottom slice the WHOLE quotient.)
  Q3  EXACT census (the bijection the Lean brick claims), exhaustive over the FULL
      {-1,0,1}-coefficient cube of length p^a: the divisible vectors are EXACTLY
      {Phi * R : R in {-1,0,1}^Q} — count 3^Q (9 at p^a = 4; 27 at p^a = 9) — and
      non-divisible vectors exist (the divisibility hypothesis is load-bearing).
  Q4  structure report: which quotients occur for REAL indicator differences —
      nonzero quotients occur (non-vacuity), and the realized set is reported
      against the full 3^Q cube.

Exact integer arithmetic throughout; no floats.
"""

import sys

# ---------- exact polynomial helpers (integer coefficients, ascending) ----------

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r

def polydivmod(num, den):
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
    num = [-1] + [0] * (n - 1) + [1]
    den = [1]
    for d in range(1, n):
        if n % d == 0:
            den = polymul(den, cyclotomic(d))
    q, r = polydivmod(num, den)
    assert all(c == 0 for c in r), f"Phi_{n} division not exact"
    _cyc_cache[n] = q
    return q

def power_residues(n):
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

def grid_columns(mask, n, N, M):
    """CRT grid (N x M), gridMap(j,c) = (j*M + c*N) % n."""
    cols = []
    for c in range(M):
        col = frozenset(j for j in range(N) if (mask >> ((j * M + c * N) % n)) & 1)
        cols.append(col)
    return cols

def trim(v):
    v = v[:]
    while len(v) > 1 and v[-1] == 0:
        v.pop()
    return v

def degree(v):
    v = trim(v)
    return -1 if v == [0] else len(v) - 1

def main():
    ok = True

    def check(cond, label):
        nonlocal ok
        print(("PASS" if cond else "FAIL"), label)
        if not cond:
            ok = False

    # ---------------- Q1 + Q4: real indicator differences, exhaustive ----------------
    for n, (Pa, M) in ((12, (4, 3)), (18, (9, 2))):
        pp = prime_factors(Pa)[0]      # the prime p with Pa = p^a
        Q = Pa // pp                    # p^(a-1)
        phi = [0] * (Q * (pp - 1) + 1)  # Phi_{p^a} = Sum_{t<p} X^(t*Q)
        for t in range(pp):
            phi[t * Q] = 1
        assert trim(polymul([1], cyclotomic(Pa))) == trim(phi), "packet != Phi_{p^a}"
        van = vanishing_subsets(n)
        pairs = bad_div = bad_deg = bad_coef = bad_slice = bad_recon = 0
        quotients = {}
        for mask in van:
            cols = grid_columns(mask, n, Pa, M)
            for i in range(M):
                for j in range(M):
                    if i == j:
                        continue
                    X, Y = cols[i], cols[j]
                    d = [(1 if e in X else 0) - (1 if e in Y else 0)
                         for e in range(Pa)]
                    pairs += 1
                    num = trim(d)
                    if num == [0]:
                        R, rem = [0], [0]
                    else:
                        R, rem = polydivmod(num, phi)
                    if any(c != 0 for c in rem):
                        bad_div += 1
                        continue
                    if degree(R) >= Q:
                        bad_deg += 1
                    if any(c not in (-1, 0, 1) for c in R):
                        bad_coef += 1
                    Rpad = R + [0] * (Q - len(R)) if len(R) < Q else R
                    if any(Rpad[s] != d[s] for s in range(Q)):
                        bad_slice += 1
                    recon = [0] * Pa
                    for s in range(Q):
                        if d[s]:
                            for t in range(pp):
                                recon[s + t * Q] += d[s]
                    if recon != d:
                        bad_recon += 1
                    quotients[tuple(Rpad[:Q])] = quotients.get(tuple(Rpad[:Q]), 0) + 1
        check(bad_div == 0,
              f"Q1 n={n}: all {pairs} column-pair differences divisible by Phi_{Pa} "
              f"({len(van)} vanishing subsets, exhaustive) [O87 C6 re-verified]")
        check(bad_deg == 0,
              f"Q1 n={n}: every quotient has deg < Q = {Q} (the degree-bound brick)")
        check(bad_coef == 0,
              f"Q1 n={n}: every quotient coefficient in {{-1,0,1}}")
        check(bad_slice == 0,
              f"Q1 n={n}: quotient = bottom slice of d (R[s] = d[s], s < {Q})")
        check(bad_recon == 0,
              f"Q1 n={n}: d = Sum_s d[s]*X^s*Phi reconstructs exactly "
              f"(rotated-packet combination)")
        nonzero = {k: v for k, v in quotients.items() if any(k)}
        check(len(nonzero) > 0,
              f"Q4 n={n}: nonzero quotients occur (non-vacuity); realized "
              f"{len(quotients)}/{3 ** Q} of the {{-1,0,1}}^{Q} cube; "
              f"distinct nonzero: {sorted(nonzero)}")

    # ---------------- Q2: degree hypothesis load-bearing ----------------
    for Pa, pp in ((4, 2), (9, 3)):
        Q = Pa // pp
        phi = [0] * (Q * (pp - 1) + 1)
        for t in range(pp):
            phi[t * Q] = 1
        d = polymul(phi, [0] * Q + [1])      # Phi * X^Q, deg = Pa (NOT < Pa)
        assert all(c in (0, 1) for c in d)
        R, rem = polydivmod(trim(d), phi)
        check(all(c == 0 for c in rem) and degree(R) == Q,
              f"Q2 p^a={Pa}: d = Phi*X^{Q} (deg {degree(trim(d))} = p^a) is divisible "
              f"but quotient deg = {degree(R)} = Q — deg d < p^a is load-bearing")
        dpad = d + [0] * max(0, (Pa + 1) - len(d))
        # finding: the bottom-slice identity holds for ANY quotient (no reach-down)
        check(all((R + [0] * Q)[s] == dpad[s] for s in range(Q)),
              f"Q2 p^a={Pa}: bottom-slice identity R[s]=d[s] holds even here "
              f"(unconditional in the quotient; the degree bound's job is to make "
              f"the bottom slice the WHOLE quotient)")
        recon = [0] * (Pa + 1)
        for s in range(Q):
            if dpad[s]:
                for t in range(pp):
                    recon[s + t * Q] += dpad[s]
        check(recon != dpad,
              f"Q2 p^a={Pa}: rotated-packet combination with shifts < Q FAILS "
              f"without deg d < p^a (load-bearing)")

    # ---------------- Q3: exact census over the full {-1,0,1} cube ----------------
    for Pa, pp in ((4, 2), (9, 3)):
        Q = Pa // pp
        phi = [0] * (Q * (pp - 1) + 1)
        for t in range(pp):
            phi[t * Q] = 1
        divisible = set()
        total = 3 ** Pa
        for code in range(total):
            v, c = [], code
            for _ in range(Pa):
                v.append(c % 3 - 1)
                c //= 3
            num = trim(v)
            if num == [0]:
                divisible.add(tuple(v))
                continue
            _, rem = polydivmod(num, phi)
            if all(c == 0 for c in rem):
                divisible.add(tuple(v))
        expect = set()
        for code in range(3 ** Q):
            R, c = [], code
            for _ in range(Q):
                R.append(c % 3 - 1)
                c //= 3
            prod = polymul(phi, R) if any(R) else [0]
            prod = prod + [0] * (Pa - len(prod))
            expect.add(tuple(prod[:Pa]))
        check(divisible == expect and len(divisible) == 3 ** Q,
              f"Q3 p^a={Pa}: divisible {{-1,0,1}}-vectors (deg < p^a) = exactly "
              f"{{Phi*R : R in {{-1,0,1}}^{Q}}}, count {len(divisible)} = 3^{Q} "
              f"of {total} (bijection; non-divisible exist: divisibility load-bearing)")

    print("OVERALL:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
