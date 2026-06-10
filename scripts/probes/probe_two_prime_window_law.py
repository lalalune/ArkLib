#!/usr/bin/env python3
"""Probe for the TWO-PRIME WINDOW LAW (O97 candidate) — falsify BEFORE Lean.

O95 named the separation between `MixedRadixTower.two_prime_tower_conditional`
and an unconditional tower: the `t > 1` window law.  This probe tests the
candidate proof route that closes it from the LANDED O94 classification alone:

THE RUNG (sparse window, the new theorem):
  n = p^a * q^b (p != q primes, a >= 1, b >= 0), T subset of mu_n, char 0.
  If  Sum_{y in T} y^(q^c) = 0  for ALL c with 0 <= c <= b,
  then T is mu_p-closed (exponent shift e -> (e + n/p) % n maps T into T).

  Proof route under test: c=0 vanishing => O94 disjoint packet decomposition;
  exponents q^c kill mu_p-packets (p coprime to q^c => full geometric sum) and
  collapse each mu_q-packet to q * (spectrum point)^(q^(c-1)); the spectrum is
  COLLISION-FREE (canonical bases are < n/q, so q*base < n pins them); the
  spectrum is a vanishing subset of mu_(n/q) inheriting the window one level
  down => induction on b, bottoming at Lam-Leung prime powers (b = 0).

THE CAPSTONE (interval window, the unconditional tower):
  with W(n) = max(p^(a-1)*(q^b+1), q^(b-1)*(p^a+1)), a vanishing interval
  window 1 <= j < W forces closure under the FULL mu_n, i.e. T in {0, mu_n}
  at exact level n = p^a*q^b.  (Discharges hBasep with wp k = q^b+1 and
  hBaseq with wq k = p^a+1 in the conditional tower.)

Checks (exit 0 iff all pass; exact integer arithmetic mod Phi_n, no floats):
  R1  RUNG, exhaustive: at n = 12, 18, 20, 24 every subset vanishing on the
      sparse window {q^c : c <= b} is mu_p-closed; family counted, nontrivial.
  R2  RUNG, swapped orientation (mu_q-closure from {p^c : c <= a}) likewise.
  R3  RUNG sharpness: dropping the TOP exponent q^b admits a violator
      (the rotated mu_(q^b)-coset), so the sparse window is minimal-in-length.
  C1  CAPSTONE, exhaustive: window {1..W-1} forces T in {empty, full}.
  C2  CAPSTONE sharpness margin: the largest t with a nontrivial survivor on
      window {1..t} is recorded; asserts t < W (my window suffices) and
      reports W - 1 - t (the interval slack; 0 = tight).
  D1  Deep point n = 36 (a = b = 2), full MITM census: R1/R2/C1 on all
      vanishing masks (the only test point with BOTH exponents >= 2).

NOT proved here (named): the Lean assembly itself; this probe gates it.
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
    """All masks with Sum zeta^e = 0, full 2^n space, meet-in-the-middle."""
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
    out = []
    for hv, hms in hi.items():
        need = tuple(-c for c in hv)
        if need in lo:
            for hm in hms:
                for lm in lo[need]:
                    out.append((hm << lo_bits) | lm)
    return out


def mask_vanishes_at(mask, j, table, deg, n):
    """Does Sum_{e in mask} zeta^(j*e) = 0 (exact, mod Phi_n)?"""
    v = [0] * deg
    mm = mask
    while mm:
        b = (mm & -mm).bit_length() - 1
        t = table[(j * b) % n]
        for i in range(deg):
            v[i] += t[i]
        mm &= mm - 1
    return all(c == 0 for c in v)


def mu_d_closed(mask, n, d):
    """Closure of the exponent mask under e -> (e + n/d) % n."""
    step = n // d
    mm = mask
    while mm:
        b = (mm & -mm).bit_length() - 1
        if not (mask >> ((b + step) % n)) & 1:
            return False
        mm &= mm - 1
    return True


def rotated_coset_mask(n, d, r):
    """Exponent mask of the rotated mu_d-coset {r + t*(n/d) : t < d}."""
    m = 0
    for t in range(d):
        m |= 1 << ((r + t * (n // d)) % n)
    return m


def run_point(n, p, a, q, b, vans=None):
    print(f"-- n = {n} = {p}^{a} * {q}^{b} --")
    table, deg = root_power_table(n)
    if vans is None:
        vans = vanishing_masks(n)
    print(f"   vanishing masks at j=1: {len(vans)}")

    # R1: sparse rung window {q^c : c <= b} => mu_p-closed
    window = [q ** c for c in range(b + 1)]
    cands = [m for m in vans
             if all(mask_vanishes_at(m, j, table, deg, n) for j in window[1:])]
    bad = [m for m in cands if not mu_d_closed(m, n, p)]
    nontriv = [m for m in cands if m != 0 and m != (1 << n) - 1]
    check(f"R1 rung mu_{p}-closure from window {window}", not bad,
          f"candidates={len(cands)} nontrivial={len(nontriv)} violators={len(bad)}")
    check(f"R1 rung family nontrivial", len(nontriv) > 0)

    # R2: swapped rung {p^c : c <= a} => mu_q-closed
    window_q = [p ** c for c in range(a + 1)]
    cands_q = [m for m in vans
               if all(mask_vanishes_at(m, j, table, deg, n) for j in window_q[1:])]
    bad_q = [m for m in cands_q if not mu_d_closed(m, n, q)]
    nontriv_q = [m for m in cands_q if m != 0 and m != (1 << n) - 1]
    check(f"R2 rung mu_{q}-closure from window {window_q}", not bad_q,
          f"candidates={len(cands_q)} nontrivial={len(nontriv_q)} violators={len(bad_q)}")

    # R3: sharpness — drop top exponent q^b; rotated mu_(q^b)-coset violates
    wit = rotated_coset_mask(n, q ** b, 1)
    short = window[:-1]
    wit_vanishes = all(mask_vanishes_at(wit, j, table, deg, n) for j in short)
    wit_open = not mu_d_closed(wit, n, p)
    check(f"R3 sharpness: mu_{q**b}-coset vanishes on {short} but not mu_{p}-closed",
          wit_vanishes and wit_open)
    # and the swapped sharpness control
    wit2 = rotated_coset_mask(n, p ** a, 1)
    short2 = window_q[:-1]
    wit2_ok = (all(mask_vanishes_at(wit2, j, table, deg, n) for j in short2)
               and not mu_d_closed(wit2, n, q))
    check(f"R3' sharpness: mu_{p**a}-coset vanishes on {short2} but not mu_{q}-closed",
          wit2_ok)

    # C1: capstone interval window {1..W-1} => empty or full
    W = max(p ** (a - 1) * (q ** b + 1), q ** (b - 1) * (p ** a + 1))
    full = (1 << n) - 1
    surv = [m for m in vans
            if all(mask_vanishes_at(m, j, table, deg, n) for j in range(2, W))]
    bad_c = [m for m in surv if m != 0 and m != full]
    check(f"C1 capstone window {{1..{W - 1}}} forces empty/full", not bad_c,
          f"survivors={len(surv)} nontrivial={len(bad_c)}")

    # C2: sharpness margin — largest t with a nontrivial survivor on {1..t}
    t_sharp = 0
    for t in range(1, W):
        s = [m for m in vans if m != 0 and m != full
             and all(mask_vanishes_at(m, j, table, deg, n) for j in range(2, t + 1))]
        if s:
            t_sharp = t
        else:
            break
    check(f"C2 sharp threshold t={t_sharp} < W-1={W - 1} margin={W - 1 - t_sharp}",
          t_sharp < W, f"(interval slack {W - 1 - t_sharp}; 0 = tight)")
    print()


def main():
    print("== TWO-PRIME WINDOW LAW probe (rung + capstone, falsify-first) ==\n")
    run_point(12, 2, 2, 3, 1)
    run_point(18, 2, 1, 3, 2)
    run_point(20, 2, 2, 5, 1)
    run_point(24, 2, 3, 3, 1)
    # D1: the deep point a = b = 2 (full MITM census, the only both->=2 point)
    print("-- deep point n = 36 (full MITM census; this takes a minute) --")
    vans36 = vanishing_masks(36)
    run_point(36, 2, 2, 3, 2, vans=vans36)

    if FAIL:
        print(f"FAILURES: {FAIL}")
        sys.exit(1)
    print("ALL CHECKS PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
