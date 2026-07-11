#!/usr/bin/env python3
"""
probe_dooriv_greedy_heavier_half_descent.py  (#444/#464, door-(iv) Lane 1)

THE UNDER-PROBED QUESTION (builds on c1aae3d7e / 2c3e1aad6, NOT a re-probe):
  Prior FLEET-PROVEN facts at the worst frequency b*:
    (F1) the two index-2 coset halves A=Σ_{x∈μ_{n/2}} e_p(b*x), B=Σ_{x∈h·μ_{n/2}} e_p(b*x)
         are COHERENT (ρ(b*)=|A+B|/(|A|+|B|)=1 exactly, ∠(A,B)=0) ⟹ M(b*)=|A|+|B| EXACTLY.
    (F2) they are STRICTLY IMBALANCED and the imbalance GROWS with n (heavier side unstructured).

  So at b*, M(n) = |A|+|B| = |A_heavy|·(1 + r),  r = |A_light|/|A_heavy| < 1 (and r→? as n grows).

  THE NEW QUESTION (genuinely thinner controlling object?):
    Each half is ITSELF a period over the thinner subgroup μ_{n/2} at the SAME frequency b*.
    Define the GREEDY HEAVIER-HALF DESCENT: start at level a (n=2^a), at each level keep the
    heavier of the two μ_{n/2}-coset halves and recurse on it, all at the FIXED worst frequency b*.
    This produces a chain  H_a ≥ H_{a-1} ≥ ... ≥ H_0=1  of half-magnitudes and "lighter/heavier"
    ratios r_a, r_{a-1}, ... at each split.

    Q-A (telescoping):   is  M(n) = |A|+|B|  controlled by the PRODUCT  Π_i (1 + r_i)  times the
                          terminal heavier magnitude?  i.e. does the prize reduce to a 1-D descent
                          product rather than the full 2^a-leaf tower?
    Q-B (the lever):     the prize needs M(n) ≤ C√(n log p). If the greedy product Π(1+r_i)
                          stays O(1)·poly(a) while the terminal heavy magnitude stays O(√n),
                          that would be a structurally THINNER target. Measure whether Π(1+r_i)
                          grows like √n (no help — same wall) or is genuinely sub-√n (a lever).
    Q-C (honesty / wall):does the greedy heavier branch at b* even TRACK the worst frequency at
                          the sub-level, or does the worst-b DRIFT (already proven NON-nested,
                          _DoorIVWorstBNonNested)? If b* is not worst at the sub-level, the greedy
                          descent is at a NON-adversarial frequency downstream ⟹ it LOWER-bounds,
                          not upper-bounds, the sub-period ⟹ the descent product does NOT majorize
                          M(n/2). That is the honest wall (and exactly why naive descent fails).

EXACT setup: PROPER μ_n (n=2^a), p≡1 mod n, p≫n³, m=(p-1)/n preferentially ODD, NEVER n=q-1.
n=8..128, multiple structured primes. FULL coset scan for the worst-b where feasible (n≤32),
large-prime exact otherwise. NO moment, NO completion, NO Lean unless a real structure survives.
"""
import cmath, math, sys
from sympy import factorint, isprime


def primitive_root(p):
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")


def find_prime(n, beta, parity_odd_m=True, start_mult=None):
    """Find prime p ≡ 1 mod n, p ~ n^beta, with m=(p-1)/n preferentially odd."""
    target = int(round(n ** beta))
    # we want p = k*n + 1 prime, k = m = (p-1)/n; prefer m odd
    k0 = max(3, target // n)
    for dk in range(0, 200000):
        for k in (k0 + dk, k0 - dk):
            if k < 3:
                continue
            if parity_odd_m and k % 2 == 0:
                continue
            p = k * n + 1
            if p > n and isprime(p):
                return p, k  # k == m
    raise RuntimeError(f"no prime for n={n}, beta={beta}")


def mu_n_elements(p, n):
    """The multiplicative subgroup μ_n < F_p* of order n (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of μ_n
    elts = []
    cur = 1
    for _ in range(n):
        elts.append(cur)
        cur = (cur * h) % p
    return elts, g


def period(b, elts, p):
    """η_b = Σ_{x∈elts} e_p(b x)."""
    s = 0.0 + 0.0j
    for x in elts:
        ang = 2.0 * math.pi * ((b * x) % p) / p
        s += cmath.exp(1j * ang)
    return s


def worst_b_full(p, n, elts):
    """FULL scan over coset reps of F_p*/μ_n: return b* maximizing |η_b|, and M=|η_{b*}|.
    η_b is constant on μ_n-cosets, so scan one rep per coset."""
    seen = set()
    g = primitive_root(p)
    # coset reps: powers of g step by n? simpler: iterate b=1..p-1, dedupe by canonical coset rep
    best_b, best = 1, -1.0
    # canonical coset rep = min element of b*μ_n
    for b in range(1, p):
        # canonical rep of coset b·μ_n
        rep = min((b * x) % p for x in elts)
        if rep in seen:
            continue
        seen.add(rep)
        val = abs(period(b, elts, p))
        if val > best:
            best, best_b = val, b
    return best_b, best


def split_halves(elts):
    """Index-2 split μ_n = μ_{n/2} ⊔ h·μ_{n/2}.  elts is the cyclic listing [1,h,h²,...];
    μ_{n/2} = even-power elements = elts[::2] (the squares), other coset = elts[1::2]."""
    A = elts[0::2]   # μ_{n/2} (squares)
    B = elts[1::2]   # h·μ_{n/2}
    return A, B


def greedy_descent(b, elts, p):
    """At FIXED frequency b, descend always into the HEAVIER half. Returns:
       chain of (|heavy|, |light|, r=light/heavy) per level from top (n) down to 2.
       Also returns the greedy product Π(1+r_i) and terminal |heavy| (=1, a single root)."""
    cur = list(elts)
    chain = []
    while len(cur) >= 2:
        A, B = split_halves(cur)
        sA = abs(period(b, A, p))
        sB = abs(period(b, B, p))
        heavy, light = (A, B) if sA >= sB else (B, A)
        hmag, lmag = (sA, sB) if sA >= sB else (sB, sA)
        r = lmag / hmag if hmag > 0 else 0.0
        chain.append((len(cur), hmag, lmag, r))
        cur = heavy
    return chain


def sub_worst_b_full(p, sub_elts):
    """worst b for the sub-period over sub_elts (FULL coset scan w.r.t. the SUBGROUP)."""
    n2 = len(sub_elts)
    seen = set()
    best_b, best = 1, -1.0
    for b in range(1, p):
        rep = min((b * x) % p for x in sub_elts)
        if rep in seen:
            continue
        seen.add(rep)
        val = abs(period(b, sub_elts, p))
        if val > best:
            best, best_b = val, b
    return best_b, best


def coset_eq(b1, b2, sub_elts, p):
    """Is b1 in the same sub_elts-coset as b2? (i.e. b1 ≡ b2 · x for some x in <sub_elts>?)"""
    s1 = set((b1 * x) % p for x in sub_elts)
    return ((b2) % p) in s1


def main():
    print(f"{'n':>5} {'p':>12} {'beta':>5} {'M=|A|+|B|':>11} {'M/sqn':>8} "
          f"{'greedyProd':>11} {'gProd/sqn':>10} {'termHeavy':>10} "
          f"{'b*=subWorst?':>13} {'mode':>10}")
    rows = []
    for n in [8, 16, 32, 64, 128]:
        beta = 4.0
        full = (n <= 32)
        p, m = find_prime(n, beta, parity_odd_m=True)
        elts, g = mu_n_elements(p, n)
        if full:
            bstar, M = worst_b_full(p, n, elts)
        else:
            # large-n: scan a large but bounded set of coset reps (deterministic stride)
            best_b, best = 1, -1.0
            seen = set()
            stride = max(1, (p - 1) // 200000)
            for b in range(1, p, stride):
                rep = min((b * x) % p for x in elts)
                if rep in seen:
                    continue
                seen.add(rep)
                v = abs(period(b, elts, p))
                if v > best:
                    best, best_b = v, b
            bstar, M = best_b, best
        sqn = math.sqrt(n)
        chain = greedy_descent(bstar, elts, p)
        gprod = 1.0
        for (_, hmag, lmag, r) in chain:
            gprod *= (1.0 + r)
        term_heavy = chain[-1][1] if chain else 1.0  # terminal |heavy| (single root => 1)
        # Q-C: at the FIRST split, is b* also the worst-b for the heavier sub-subgroup?
        A, B = split_halves(elts)
        sA, sB = abs(period(bstar, A, p)), abs(period(bstar, B, p))
        heavy_sub = A if sA >= sB else B
        if full:
            sub_bw, sub_M = sub_worst_b_full(p, heavy_sub)
            tracks = coset_eq(bstar, sub_bw, heavy_sub, p) or abs(abs(period(bstar, heavy_sub, p)) - sub_M) < 1e-9
            tracks_str = "YES" if tracks else "NO"
        else:
            tracks_str = "n/a"
        mode = "FULL" if full else "stride"
        print(f"{n:>5} {p:>12} {beta:>5.1f} {M:>11.4f} {M/sqn:>8.4f} "
              f"{gprod:>11.4f} {gprod/sqn:>10.4f} {term_heavy:>10.4f} "
              f"{tracks_str:>13} {mode:>10}")
        rows.append((n, p, M, M/sqn, gprod, gprod/sqn, tracks_str))

    print()
    print("READING:")
    print("- greedyProd = Π_i (1 + r_i), r_i=light/heavy at each level along the always-heavier chain at b*.")
    print("- termHeavy ≈ 1 (single root). So the greedy descent VALUE = termHeavy·greedyProd is the")
    print("  product, NOT the true M (the descent at a FIXED b is a strict LOWER path: each level")
    print("  keeps only one half ⟹ greedyProd·termHeavy ≤ M is NOT guaranteed; we measure the gap).")
    print("- Q-B lever test: does greedyProd/sqn stay BOUNDED (→ const) as n grows? If it grows ~√n")
    print("  (gProd/sqn → const>0 i.e. gProd~n), the descent product carries the SAME wall (no help).")
    print("  If gProd is genuinely sub-√n (gProd/sqn → 0), the 1-D descent is a THINNER object (a lever).")
    print("- Q-C 'b*=subWorst?': if NO at the first split, b* is NON-adversarial downstream ⟹ the greedy")
    print("  chain runs at a non-worst frequency for the sub-period ⟹ it does NOT majorize M(n/2) ⟹")
    print("  the descent CANNOT telescope into an upper bound (honest wall = _DoorIVWorstBNonNested).")


if __name__ == "__main__":
    main()
