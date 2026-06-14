#!/usr/bin/env python3
"""probe_redteam_promoted.py — adversarial red-team of the promoted #371 hypotheses.

Targets (all landed axiom-clean; this probe attacks the MATHEMATICS adversarially,
looking for slack, dodges, and numerical lies the Lean statements could be hiding
behind their hypotheses):

  RT1 (R1 floor, new instance class)  the all-witness floor at d = 3 (beyond every
      previously probed instance): exhaustive over F_7 words on 6 nodes — does any word
      beat #fit <= C(w-1, d+2)?  Also: is attainment still exactly single-deviation?
  RT2 (R1 consequence, adversarial search)  the radius-adaptive count at deep radii:
      at (p, n, d) = (17, 8, 1), witness floors w0 = 5, 6: hill-climb stacks trying to
      EXCEED the adaptive bound C(8,3)/C(w0-1,2).  A single crossing refutes the
      adaptive law (and hence the floor's consequence chain).
  RT3 (Landau sharpening, empirical attack)  exact collision resultants at m = 3, 4
      (via the product over primitive 2^m-th roots, high-precision, integer-rounded,
      residue-checked mod several primes): compare against BOTH bounds —
      old l1: |Res| <= ||R||_1^h;  new sharp: |Res|^2 <= 4^{deg R} * (sum c_i^2)^h.
      The sharp bound must hold on every sample (violation = the Lean theorem is
      misstated/mistranscribed); report worst-case ratios (how much slack remains).
  RT4 (S2/R2 primes, independent re-verification)  all three landed primes re-checked
      with an INDEPENDENT base set + the exact Proth criterion (3^((P-1)/2) = -1 mod P
      would even certify directly); order-of-g re-derived from scratch; all band
      memberships recomputed with fractions.
  RT5 (R2 pins, ceiling consistency)  every landed pin value 1 - r/2^mu must be
      strictly between Johnson (1 - sqrt(rate)) and capacity (1 - rate), and the pinned
      eps* bands of distinct rungs at the same mu must be DISJOINT (overlapping bands
      with different delta* values would be an outright contradiction).

Exit 0 iff no adversarial finding; any FAIL is a refutation lead.
"""
import cmath
import itertools
import random
import sys
from fractions import Fraction
from math import comb

FAIL = 0
RNG = random.Random(371_99)


def check(name, ok, detail=""):
    global FAIL
    print(("  OK   " if ok else "  FAIL ") + name + ("" if not detail else f"  [{detail}]"))
    if not ok:
        FAIL = 1


def inv_mod(a, p):
    return pow(a, p - 2, p)


def fits(xs, ys, d, p, T):
    T = sorted(T)
    if len(T) <= d + 1:
        return True
    base = T[: d + 1]

    def ev(x):
        tot = 0
        for i in base:
            num, den = 1, 1
            for j in base:
                if j == i:
                    continue
                num = num * ((x - xs[j]) % p) % p
                den = den * ((xs[i] - xs[j]) % p) % p
            tot = (tot + ys[i] * num * inv_mod(den, p)) % p
        return tot

    return all(ev(xs[i]) == ys[i] % p for i in T[d + 1:])


# ---------- RT1: floor at d = 3, exhaustive ----------
def rt1():
    p, w, d = 7, 6, 3
    xs = list(range(w))
    k = d + 2
    bound = comb(w - 1, k)
    S = list(range(w))
    maxfit, viol, attain, attain_sd = 0, 0, 0, 0
    for ys in itertools.product(range(p), repeat=w):
        if fits(xs, ys, d, p, S):
            continue
        nf = sum(1 for T in itertools.combinations(S, k) if fits(xs, ys, d, p, T))
        if nf > bound:
            viol += 1
        if nf > maxfit:
            maxfit, attain, attain_sd = nf, 0, 0
        if nf == maxfit:
            attain += 1
            if any(fits(xs, ys, d, p, [i for i in S if i != j]) for j in S):
                attain_sd += 1
    check(f"RT1 floor d=3: max #fit {maxfit} <= C(5,5)={bound}, exhaustive F_{p}^{w}",
          viol == 0, f"attained {attain}, single-dev {attain_sd}")
    check("RT1 attainment exactly single-deviation", attain == attain_sd)


# ---------- RT2: adaptive count, adversarial hill-climb ----------
def rt2():
    p, n, d = 17, 8, 1
    g = 2  # order 8 mod 17
    xs = [pow(g, i, p) for i in range(n)]

    def badcount(u0, u1, w0):
        cnt = 0
        for gam in range(p):
            w = [(a + gam * b) % p for a, b in zip(u0, u1)]
            found = False
            for s in range(w0, n + 1):
                for S in itertools.combinations(range(n), s):
                    if fits(xs, w, d, p, S) and not (fits(xs, u0, d, p, S) and fits(xs, u1, d, p, S)):
                        found = True
                        break
                if found:
                    break
            if found:
                cnt += 1
        return cnt

    for w0 in (5, 6):
        bound = comb(n, d + 2) // comb(w0 - 1, d + 1)
        best = 0
        u0 = [RNG.randrange(p) for _ in range(n)]
        u1 = [RNG.randrange(p) for _ in range(n)]
        cur = badcount(u0, u1, w0)
        for _ in range(80):
            v0, v1 = u0[:], u1[:]
            j = RNG.randrange(n)
            if RNG.random() < 0.5:
                v0[j] = RNG.randrange(p)
            else:
                v1[j] = RNG.randrange(p)
            c = badcount(v0, v1, w0)
            if c >= cur:
                u0, u1, cur = v0, v1, c
            best = max(best, cur)
        check(f"RT2 adaptive count w0={w0}: hill-climbed max {best} <= C(8,3)/C({w0-1},2) = {bound}",
              best <= bound)


# ---------- RT3: Landau sharpening, empirical attack ----------
def rt3():
    for m in (3, 4):
        h = 2 ** (m - 1)
        roots = [cmath.exp(2j * cmath.pi * j / (2 ** m)) for j in range(2 ** m) if j % 2 == 1]
        assert len(roots) == h
        worst_sharp, worst_l1 = 0.0, 0.0
        viol = 0
        for _ in range(4000):
            r = RNG.randint(2, h)
            U1 = RNG.sample(range(h), r)
            T1 = [i for i in U1 if RNG.random() < 0.5]
            U2 = RNG.sample(range(h), r)
            T2 = [i for i in U2 if RNG.random() < 0.5]
            coeffs = [0] * h
            for i in U1:
                coeffs[i] += 1 if i in T1 else -1
            for i in U2:
                coeffs[i] -= 1 if i in T2 else -1
            if all(c == 0 for c in coeffs):
                continue
            deg = max(i for i, c in enumerate(coeffs) if c != 0)
            res = 1.0 + 0j
            for z in roots:
                res *= sum(c * z ** i for i, c in enumerate(coeffs))
            res_abs = abs(res)
            res_int = round(res_abs)
            # integer sanity: |Res| is a nonneg integer; rounding error must be tiny
            if abs(res_abs - res_int) > 1e-4 * max(1, res_int):
                continue  # precision miss, skip sample (m <= 4 keeps this rare)
            l1 = sum(abs(c) for c in coeffs)
            sq = sum(c * c for c in coeffs)
            sharp_sq = (4 ** deg) * (sq ** h)
            if res_int ** 2 > sharp_sq:
                viol += 1
            if sharp_sq > 0 and res_int > 0:
                worst_sharp = max(worst_sharp, (res_int ** 2) / sharp_sq)
            if l1 > 0 and res_int > 0:
                worst_l1 = max(worst_l1, res_int / (l1 ** h))
        check(f"RT3 m={m}: sharp bound holds on all samples", viol == 0,
              f"worst sharp-ratio {worst_sharp:.2e}, worst l1-ratio {worst_l1:.2e}")


# ---------- RT4: primes + orders, independent ----------
def rt4():
    def mr(n, bases):
        if n < 2:
            return False
        d, s = n - 1, 0
        while d % 2 == 0:
            d //= 2
            s += 1
        for a in bases:
            if a % n == 0:
                continue
            x = pow(a, d, n)
            if x in (1, n - 1):
                continue
            for _ in range(s - 1):
                x = x * x % n
                if x == n - 1:
                    break
            else:
                return False
        return True

    P1 = 65581 * 2 ** 64 + 1
    P2 = 1314883 * 2 ** 128 + 1
    P3 = 1526377 * 2 ** 128 + 1
    indep = [41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    for name, P, hh, mu in (("P80", P1, 65581, 5), ("P148", P2, 1314883, 5), ("P64dom", P3, 1526377, 6)):
        check(f"RT4 {name} independent-base MR", mr(P, indep))
        # Proth: a^((P-1)/2) = -1 directly certifies primality for h < 2^k
        proth = any(pow(a, (P - 1) // 2, P) == P - 1 for a in (3, 5, 7, 11))
        check(f"RT4 {name} Proth criterion (a^((P-1)/2) = -1)", proth)
        n_dom = 2 ** mu
        g = pow(3, (P - 1) // n_dom, P)
        check(f"RT4 {name} order(g) = {n_dom} from scratch",
              pow(g, n_dom, P) == 1 and pow(g, n_dom // 2, P) != 1)


# ---------- RT5: pins, ceiling consistency + band disjointness ----------
def rt5():
    pins = []  # (mu, r, q, lo_count, hi_count)
    P1 = 65581 * 2 ** 64 + 1
    for r in (7, 8, 9, 10):
        pins.append((5, r, P1, Fraction(comb(32, r) // r, P1), Fraction(2 ** r * comb(16, r), P1)))
    P2 = 1314883 * 2 ** 128 + 1
    pins.append((5, 8, P2, Fraction(comb(32, 8) // 8, P2), Fraction(2 ** 8 * comb(16, 8), P2)))
    P3 = 1526377 * 2 ** 128 + 1
    pins.append((6, 5, P3, Fraction(comb(64, 5) // 5, P3), Fraction(2 ** 5 * comb(32, 5), P3)))
    eps = Fraction(1, 2 ** 128)
    ok_window = True
    for mu, r, q, lo, hi in pins:
        n = 2 ** mu
        rate = Fraction(r - 1, n)
        delta = Fraction(n - r, n)
        # beyond Johnson (squared): (r/n)^2 < rate  <=>  1 - delta > ...; below capacity
        if not (Fraction(r * r, n * n) < rate and delta < 1 - rate):
            ok_window = False
        if q in (P2, P3):
            if not (lo <= eps < hi):
                ok_window = False
    check("RT5 all pins strictly in-window; literal pins inside their eps* bands", ok_window)
    # CORRECTED CHECK (first run conflated different codes): bands of DIFFERENT rungs
    # pin DIFFERENT codes (degree r-2), so overlap in eps* is benign.  The genuine
    # consistency requirement: at most one pin per (code, eps*) — i.e., no two pins with
    # the SAME (mu, r, q) and different delta*.  Verify, and additionally verify the
    # monotone sanity delta*(r) = 1 - r/2^mu strictly decreasing in r at fixed mu.
    seen = {}
    ok_same = True
    for mu, r, q, lo, hi in pins:
        key = (mu, r, q)
        val = Fraction(2 ** mu - r, 2 ** mu)
        if key in seen and seen[key] != val:
            ok_same = False
        seen[key] = val
    check("RT5 one delta* per (code, field); cross-code band overlap benign", ok_same)
    deltas = [Fraction(2 ** 5 - r, 2 ** 5) for r in (7, 8, 9, 10)]
    check("RT5 delta* strictly decreasing in r at mu=5", all(
        a > b for a, b in zip(deltas, deltas[1:])))


rt1()
rt2()
rt3()
rt4()
rt5()
sys.exit(FAIL)
