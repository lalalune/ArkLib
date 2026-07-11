#!/usr/bin/env python3
"""Issue #232 — O95 named brick (i): the WEIGHTED (ℕ-coefficient) packet theorems.

Falsify-first probe for the ℕ-weighted generalization of the de Bruijn packet
classification (Lam–Leung J. Algebra 1996 territory):

Part A — prime powers n = p^(a+1) ∈ {4, 8, 9, 27}:
  every ℕ-weighted vanishing sum  Σ_e w(e)·ζ_n^e = 0  should satisfy, as an IFF,
  the slice-replication / packet-combination law
        w(e + p^a mod n) = w(e)  for ALL e          (w is p^a-periodic)
  equivalently  w = Σ_{s<p^a} w(s) · packet_s  (packet_s = rotated full μ_p-packet),
  and the WEIGHT LAW  |w| = Σ_e w(e) ∈ ℕp  (p divides the total weight).
  Controls: vanishing-but-not-replicated must be 0; p ∣ |w| WITHOUT vanishing must
  exist (the weight law is one-way); toggles of planted vanishing w must not vanish.

Part B — two primes n = 12 = 2²·3 (exhaustive, entries ≤ 2) and n = 18 = 2·3²
  (planted + random sample):
  de Bruijn 1953 claims every ℕ-weighted vanishing sum at ≤ 2 prime factors is an
  ℕ-combination of rotated full prime packets:
        w = Σ_{s<n/2} a_s·1_{μ₂-packet(s)} + Σ_{s<n/3} b_s·1_{μ₃-packet(s)},  a,b ∈ ℕ.
  Weight law: |w| ∈ ℕ2 + ℕ3 = ℕ \\ {1}.
  Measure mixture witnesses (decompositions genuinely needing both packet types)
  and weighted-mixture witnesses (some coefficient ≥ 2 forced).

Exact integer arithmetic throughout: vanishing at ζ_n ⟺ Φ_n ∣ weightPoly over ℤ
(Φ_n monic = minimal polynomial of ζ_n over ℚ).  Exit 0 iff every check passes.
"""

import itertools
import random
import sys

random.seed(232)
FAIL = 0


def check(name, ok, detail=""):
    global FAIL
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name} {detail}")
    if not ok:
        FAIL += 1


# ---------- exact cyclotomic machinery ----------

def poly_divmod(num, den):
    """Exact division of int polys (den monic). Returns (quot, rem) as coeff lists."""
    num = list(num)
    dd = len(den) - 1
    while den and den[-1] == 0:
        den = den[:-1]
        dd -= 1
    assert den[-1] == 1
    quot = [0] * max(0, len(num) - dd)
    for i in range(len(num) - 1, dd - 1, -1):
        c = num[i]
        if c:
            quot[i - dd] = c
            for j in range(dd + 1):
                num[i - dd + j] -= c * den[j]
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    return quot, num


CYCLO = {1: [-1, 1]}


def cyclotomic(n):
    if n in CYCLO:
        return CYCLO[n]
    num = [0] * (n + 1)
    num[0], num[n] = -1, 1
    den = [1]
    for d in range(1, n):
        if n % d == 0:
            cd = cyclotomic(d)
            new = [0] * (len(den) + len(cd) - 1)
            for i, a in enumerate(den):
                for j, b in enumerate(cd):
                    new[i + j] += a * b
            den = new
    q, r = poly_divmod(num, den)
    assert all(c == 0 for c in r)
    CYCLO[n] = q
    return q


def vanishes(w, n):
    """Σ w[e]·ζ_n^e = 0 ⟺ Φ_n divides Σ w[e] X^e (exact)."""
    _, r = poly_divmod(list(w), cyclotomic(n))
    return all(c == 0 for c in r)


# ---------- Part A: prime powers ----------

def replicated(w, n, q):
    return all(w[e] == w[(e + q) % n] for e in range(n))


def run_prime_power(n, p, maxw, mode, samples=20000):
    q = n // p
    n_van = n_rep = 0
    bad_van_not_rep = bad_rep_not_van = bad_weight = 0
    has_div_not_van = False
    combo_fail = 0
    if mode == "exhaustive":
        space = itertools.product(range(maxw + 1), repeat=n)
    else:
        space = (tuple(random.randrange(maxw + 1) for _ in range(n))
                 for _ in range(samples))
    for w in space:
        v = vanishes(w, n)
        r = replicated(w, n, q)
        if v:
            n_van += 1
            if not r:
                bad_van_not_rep += 1
            if sum(w) % p != 0:
                bad_weight += 1
            # literal ℕ-combination reconstruction: w = Σ_{s<q} w[s]·packet_s
            rec = [0] * n
            for s in range(q):
                for t in range(p):
                    rec[s + t * q] += w[s]
            if list(w) != rec:
                combo_fail += 1
        if r:
            n_rep += 1
            if not v:
                bad_rep_not_van += 1
        if (not v) and sum(w) % p == 0 and sum(w) > 0:
            has_div_not_van = True
    label = f"n={n} (p={p}, q={q}, {mode}, maxw={maxw})"
    check(f"A {label}: vanish ⟹ replicated", bad_van_not_rep == 0,
          f"vanishing={n_van}, violations={bad_van_not_rep}")
    check(f"A {label}: replicated ⟹ vanish", bad_rep_not_van == 0,
          f"replicated={n_rep}, violations={bad_rep_not_van}")
    check(f"A {label}: weight law p ∣ |w|", bad_weight == 0,
          f"violations={bad_weight}")
    check(f"A {label}: ℕ-combination reconstructs", combo_fail == 0,
          f"failures={combo_fail}")
    check(f"A {label}: control p∣|w| WITHOUT vanishing exists", has_div_not_van,
          "(weight law is one-way)")
    if mode == "exhaustive":
        # non-vacuity only meaningful exhaustively; in sampled mode the planted
        # family (run_prime_power_planted) is the non-vacuity witness.
        check(f"A {label}: nonempty vanishing family", n_van > 1, f"count={n_van}")
    else:
        print(f"[info] {label}: random vanishing hits={n_van} "
              "(measure-zero set; teeth live in the planted run)")


def run_prime_power_planted(n, p, maxw, n_plant=2000):
    """n too big to exhaust: plant replicated w (must vanish) + toggle (must not)."""
    q = n // p
    bad_plant = bad_toggle = 0
    for _ in range(n_plant):
        base = [random.randrange(maxw + 1) for _ in range(q)]
        w = [base[e % q] for e in range(n)]
        if not vanishes(w, n):
            bad_plant += 1
        e = random.randrange(n)
        w2 = list(w)
        w2[e] += 1  # breaks replication (w2[e] != w2[(e+q)%n])
        if vanishes(w2, n):
            bad_toggle += 1
    check(f"A n={n} planted replicated vanish", bad_plant == 0,
          f"plants={n_plant}, failures={bad_plant}")
    check(f"A n={n} toggled plants do NOT vanish", bad_toggle == 0,
          f"failures={bad_toggle}")


# ---------- Part B: two primes ----------

def two_prime_decompose(w, n, p, q):
    """Try w = Σ a_s·packet_p(s) + Σ b_s·packet_q(s), a,b ∈ ℕ.
    packet_p(s) = {s + t·(n/p) : t<p}; brute-force b ∈ {0..max(w)}^(n/q).
    Returns (a, b) or None."""
    sp, sq = n // p, n // q  # steps
    mw = max(w)
    for b in itertools.product(range(mw + 1), repeat=sq):
        res = list(w)
        ok = True
        for s in range(sq):
            if b[s]:
                for t in range(q):
                    res[s + t * sq] -= b[s]
        if any(c < 0 for c in res):
            continue
        # residual must be p-fold replicated with step sp and a_s = res[s] ≥ 0
        if all(res[e] == res[(e + sp) % n] for e in range(n)):
            a = tuple(res[:sp])
            return a, b
    return None


def run_two_prime_exhaustive(n, p, q, maxw):
    n_van = 0
    bad_decomp = bad_weight = 0
    n_mix = n_weighted_mix = 0
    sp, sq = n // p, n // q
    for w in itertools.product(range(maxw + 1), repeat=n):
        if not vanishes(w, n):
            continue
        n_van += 1
        if sum(w) == 1:
            bad_weight += 1
        d = two_prime_decompose(w, n, p, q)
        if d is None:
            bad_decomp += 1
            if bad_decomp <= 3:
                print(f"    UNDECOMPOSABLE witness: w={w}")
        else:
            a, b = d
            if any(a) and any(b):
                n_mix += 1
                if max(max(a), max(b)) >= 2:
                    n_weighted_mix += 1
    label = f"B n={n}={p}^?·{q}^? exhaustive maxw={maxw}"
    check(f"{label}: every vanishing w ℕ-decomposes into packets",
          bad_decomp == 0, f"vanishing={n_van}, undecomposable={bad_decomp}")
    check(f"{label}: weight law |w| ∈ ℕ{p}+ℕ{q}", bad_weight == 0,
          f"violations={bad_weight}")
    check(f"{label}: mixture witnesses exist", n_mix > 0,
          f"mixtures={n_mix}, weighted(coeff≥2)={n_weighted_mix}")
    check(f"{label}: nonempty vanishing family", n_van > 1, f"count={n_van}")


def run_two_prime_sampled(n, p, q, maxw, n_plant=400, n_rand=4000):
    sp, sq = n // p, n // q
    bad_plant = bad_rand = 0
    n_rand_van = 0
    for _ in range(n_plant):
        # plant a random ℕ-combination of packets — must vanish AND re-decompose
        w = [0] * n
        for s in range(sp):
            c = random.randrange(maxw)
            for t in range(p):
                w[s + t * sp] += c
        for s in range(sq):
            c = random.randrange(maxw)
            for t in range(q):
                w[s + t * sq] += c
        if not vanishes(w, n):
            bad_plant += 1
            continue
        if two_prime_decompose(w, n, p, q) is None:
            bad_plant += 1
        # toggle control: one increment breaks vanishing (teeth)
        if sum(w) > 0:
            w2 = list(w)
            w2[random.randrange(n)] += 1
            if vanishes(w2, n):
                bad_plant += 1
    for _ in range(n_rand):
        w = tuple(random.randrange(maxw + 1) for _ in range(n))
        if vanishes(w, n):
            n_rand_van += 1
            if two_prime_decompose(w, n, p, q) is None or sum(w) == 1:
                bad_rand += 1
    check(f"B n={n} planted ℕ-combinations vanish+redecompose", bad_plant == 0,
          f"plants={n_plant}, failures={bad_plant}")
    check(f"B n={n} random vanishing w decompose", bad_rand == 0,
          f"random vanishing found={n_rand_van}, failures={bad_rand}")


def main():
    print("=== Part A: prime powers (weighted iff + weight law) ===")
    run_prime_power(4, 2, 3, "exhaustive")          # 4^4 = 256
    run_prime_power(8, 2, 2, "exhaustive")          # 3^8 = 6561
    run_prime_power(9, 3, 2, "exhaustive")          # 3^9 = 19683
    run_prime_power_planted(27, 3, 3)
    run_prime_power(27, 3, 3, "sampled", samples=20000)

    print("=== Part B: two primes (weighted de Bruijn structure + Lam–Leung law) ===")
    run_two_prime_exhaustive(12, 2, 3, 2)           # 3^12 = 531441
    run_two_prime_sampled(18, 2, 3, 3)

    print(f"\n{'ALL CHECKS PASS' if FAIL == 0 else f'{FAIL} CHECKS FAILED'}")
    sys.exit(0 if FAIL == 0 else 1)


if __name__ == "__main__":
    main()
