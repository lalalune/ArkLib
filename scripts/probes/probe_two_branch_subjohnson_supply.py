#!/usr/bin/env python3
"""Red-team probe (#389): the two-branch parabola word vs the conjectured
universal mean-degree law / linear capped-supply law, in the open sub-Johnson
regime t^2 < 2(k-1)n (k=2, m=1, t=4, cap=6).

Construction: split a domain D \subseteq F_p into A \sqcup B and set
    w(x) = x^2       for x in A,
    w(x) = x^2 + c   for x in B.
Every affine polynomial agrees with each branch on <= 2 points (degree-2 root
budget), so EVERY codeword agreement is <= 4 <= cap = 6: the word is
agreement-capped unconditionally, hence admissible for SubJohnsonSupplyResidual.

A line through two A-points (x1, x1^2), (x2, x2^2) has slope s = x1+x2,
intercept -x1*x2; it meets branch B where x^2 - s x + (c + x1 x2) = 0, i.e.
roots {x3, x4} with x3+x4 = x1+x2, x3 x4 = x1 x2 + c, discriminant
(x1-x2)^2 - 4c.  When the discriminant is a nonzero square and both roots lie
in B, the line carries 4 graph points: an explainable 4-core, agreement
exactly 4.

Conjectured laws under test (issue #389 thread, 2026-06-13):
  (L1) mean-degree law: Sum_{a_c >= t} a_c <= 2n  for every capped word;
  (L2) linear supply:   #explainable 4-cores <= ~1.45*(n/cap)*C(cap,t) = 3.625n.

Prediction: both FALSE once n^3 >> c*q^2 (count ~ C(|A|,2)/8 for random
splits), invisible to the previous censuses (which stopped at n=24, q=31 =
exactly the crossover).  Exact counting, no sampling.
"""

import random
import sys
from itertools import combinations


def legendre(a, p):
    if a % p == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def sqrt_mod(a, p):
    """Tonelli-Shanks; p odd prime, a a QR."""
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    # general Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r


def exact_supply(p, D, A, c):
    """Exact per-word stats for the two-branch word on domain D = A | B.

    Returns dict with: n, lines4 (#4-rich lines = #explainable 4-cores),
    sum_a (Sum of a_c over the >= 4 family), max_a (cap check), and the full
    line census computed from ALL pairs (verification that no line exceeds 4).
    """
    A = set(A)
    D = list(D)
    B = set(D) - A
    n = len(D)
    w = {x: (x * x + (c if x in B else 0)) % p for x in D}
    # exact line census over all pairs (slope, intercept) -> count
    from collections import defaultdict
    pair_count = defaultdict(int)
    for x, y in combinations(D, 2):
        s = ((w[x] - w[y]) * pow(x - y, -1, p)) % p
        b = (w[x] - s * x) % p
        pair_count[(s, b)] += 1
    # a_c from pair count: C(a,2) = pc  =>  a = (1+sqrt(1+8 pc))/2
    lines = {}
    for key, pc in pair_count.items():
        a = int((1 + (1 + 8 * pc) ** 0.5) / 2 + 1e-9)
        assert a * (a - 1) // 2 == pc, (key, pc)
        lines[key] = a
    fam = {key: a for key, a in lines.items() if a >= 4}
    max_a = max(lines.values()) if lines else 0
    # supply = number of explainable 4-cores = Sum C(a,4)
    from math import comb
    supply = sum(comb(a, 4) for a in fam.values())
    return {
        "n": n,
        "lines4": len(fam),
        "supply": supply,
        "sum_a": sum(fam.values()),
        "max_a": max_a,
    }


def predicted_count(p, D, A, c):
    """Exact count of A-pairs whose B-branch completion lands in B (the
    constructive lower bound, no full census)."""
    B = set(D) - set(A)
    cnt = 0
    for x1, x2 in combinations(sorted(A), 2):
        disc = ((x1 - x2) ** 2 - 4 * c) % p
        if disc == 0 or legendre(disc, p) != 1:
            continue
        r = sqrt_mod(disc, p)
        s = (x1 + x2) % p
        inv2 = pow(2, -1, p)
        x3, x4 = (s + r) * inv2 % p, (s - r) * inv2 % p
        if x3 in B and x4 in B and x3 != x4:
            cnt += 1
    return cnt


def run_instance(p, n, c, seed=0, split="random"):
    rng = random.Random(seed)
    D = list(range(p)) if n == p else sorted(rng.sample(range(p), n))
    if split == "random":
        A = set(rng.sample(D, n // 2))
    elif split == "interval":
        A = set(D[: n // 2])
    else:
        raise ValueError(split)
    st = exact_supply(p, D, A, c)
    lb = predicted_count(p, D, A, c)
    st.update(p=p, c=c, seed=seed, split=split, lower=lb,
              two_n=2 * st["n"], lin_B=int(3.625 * st["n"]))
    return st


def main():
    print("=== two-branch parabola word: exact capped supply, k=2 m=1 t=4 cap=6 ===")
    print("law L1 (mean-degree): sum_a <= 2n ; law L2 (linear B): supply <= 3.625n")
    print()
    hdr = (f"{'p':>5} {'n':>4} {'c':>3} {'split':>8} {'4rich':>6} {'supply':>7} "
           f"{'sum_a':>6} {'2n':>5} {'L1':>9} {'linB':>6} {'L2':>9} {'max_a':>5} {'lb':>6}")
    print(hdr)
    viol1 = viol2 = 0
    rows = []
    cases = []
    # full-domain instances, growing p
    for p in [31, 41, 53, 61, 71, 101, 151, 251, 401, 601]:
        cases.append((p, p, 1, 0, "random"))
    # n < q instances
    for (p, n) in [(61, 50), (71, 60), (101, 80), (151, 120), (251, 200),
                   (401, 320), (601, 480), (101, 47), (151, 28)]:
        cases.append((p, n, 1, 0, "random"))
    # c / seed / split robustness at p = 61
    for c in [2, 3, 5]:
        cases.append((61, 61, c, 0, "random"))
    for seed in [1, 2]:
        cases.append((61, 61, 1, seed, "random"))
    cases.append((61, 61, 1, 0, "interval"))

    for (p, n, c, seed, split) in cases:
        st = run_instance(p, n, c, seed=seed, split=split)
        l1 = "VIOLATED" if st["sum_a"] > st["two_n"] else "ok"
        l2 = "VIOLATED" if st["supply"] > st["lin_B"] else "ok"
        viol1 += l1 == "VIOLATED"
        viol2 += l2 == "VIOLATED"
        assert st["max_a"] <= 6, "cap broken?!"
        assert st["lines4"] >= st["lower"], "census < constructive lower bound?!"
        print(f"{st['p']:>5} {st['n']:>4} {st['c']:>3} {st['split']:>8} "
              f"{st['lines4']:>6} {st['supply']:>7} {st['sum_a']:>6} "
              f"{st['two_n']:>5} {l1:>9} {st['lin_B']:>6} {l2:>9} "
              f"{st['max_a']:>5} {st['lower']:>6}")
        rows.append(st)
    print()
    print(f"L1 (mean-degree <= 2n) violations: {viol1}/{len(rows)}")
    print(f"L2 (supply <= 3.625n) violations:  {viol2}/{len(rows)}")
    # growth fit on the full-domain family
    full = [r for r in rows if r["n"] == r["p"] and r["c"] == 1 and r["seed"] == 0
            and r["split"] == "random"]
    print("\nfull-domain growth (supply vs n^2/64 prediction):")
    for r in full:
        pred = r["n"] ** 2 / 64
        print(f"  n={r['n']:>4}  supply={r['supply']:>6}  n^2/64={pred:8.1f} "
              f" ratio={r['supply'] / pred:5.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
