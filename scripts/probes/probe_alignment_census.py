#!/usr/bin/env python3
"""Probe (#371): the ALIGNMENT CENSUS below the boundary band.

By the universal alignment law (UniversalAlignmentLaw.lean, kernel-proven):
at agreement band a (a-1 < (1-delta)n <= a), gamma is MCA-bad iff some a-set is
gamma-aligned with a nondegenerate tuple, and

    #bad(band a) <= #{alignable a-sets};  each alignable a-set pins one gamma.

An a-set is alignable iff all its nondegenerate (k+1)-sub-tuples share ONE ratio
-e0(T)/e1(T), where e_j(T) = the divided difference [x_{t0..tk}] u_j (proportional
to the bordered-Vandermonde residual; proportionality constant cancels in ratios).

QUESTIONS (pre-registered):
 (Q1) Supply decay: how fast does #alignable a-sets fall as a goes k+1 -> k+2 -> ...?
      (The deployed threshold radius = deepest band with supply above eps*q.)
 (Q2) Which lines are extremal BELOW the boundary - the boundary winners
      (high-frequency character lines), KKH26's adjacent line, or far-generic?
 (Q3) #bad(band a) = #distinct pinned ratios: how does the bad count collapse
      with depth? Where does it hit O(n)?

Setup: n=16, k=4 (rate 1/4), p in {12289, 65537}, bands a = 5 (boundary), 6, 7, 8.
"""
import itertools, random, sys
from collections import defaultdict

N = 16
K = 4  # dimension; deg <= 3; tuples have k+1 = 5 points


def find_g(p, n):
    for h in range(2, 500):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    raise ValueError


def divided_diff(pts_idx, u, xs, p):
    """[x_{t0},...,x_{tk}] u = sum u(ti) / prod_{j != i} (x_i - x_j)  (mod p)."""
    total = 0
    for i in pts_idx:
        den = 1
        for j in pts_idx:
            if i == j: continue
            den = den * ((xs[i] - xs[j]) % p) % p
        total = (total + u[i] * pow(den, -1, p)) % p
    return total


def census(u0, u1, xs, p, bands):
    """for each band a: (#alignable a-sets, #distinct pinned gammas)."""
    n = len(xs)
    # precompute divided differences on all (k+1)-tuples
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), K + 1):
        e0[T] = divided_diff(T, u0, xs, p)
        e1[T] = divided_diff(T, u1, xs, p)

    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if b_ != 0:
            return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'NOROOT'  # degenerate / never-fits

    out = {}
    for a in bands:
        alignable = 0
        gammas = set()
        for S in itertools.combinations(range(n), a):
            r = None
            ok = True
            any_nd = False
            for T in itertools.combinations(S, K + 1):
                rt = ratio(T)
                if rt is None:
                    continue  # degenerate sub-tuple: free
                if rt == 'NOROOT':
                    ok = False; break  # e1=0, e0!=0: fits no gamma
                any_nd = True
                if r is None:
                    r = rt
                elif r != rt:
                    ok = False; break
            if ok and any_nd:
                alignable += 1
                gammas.add(r)
        out[a] = (alignable, len(gammas))
    return out


def charline(a, b, xs, p):
    return ([pow(x, a, p) for x in xs], [pow(x, b, p) for x in xs])


def run_block(K_local, bands, tests_spec, p, rng):
    global K
    K = K_local
    g = find_g(p, N)
    xs = [pow(g, i, p) for i in range(N)]
    assert len(set(xs)) == N
    print(f"\n==== k = {K_local}, p = {p}, g = {g} ====")
    print(f"{'line':>17} | " + " | ".join(f"a={a}: align/#bad" for a in bands))
    tests = []
    for name, spec in tests_spec:
        if spec == 'random':
            u0 = [rng.randrange(p) for _ in range(N)]
            u1 = [rng.randrange(p) for _ in range(N)]
            tests.append((name, (u0, u1)))
        else:
            a_, b_ = spec
            tests.append((name, charline(a_, b_, xs, p)))
    for name, (u0, u1) in tests:
        c = census(u0, u1, xs, p, bands)
        row = " | ".join(f"{c[a][0]:>6}/{c[a][1]:<5}" for a in bands)
        print(f"{name:>17} | {row}", flush=True)


def main():
    rng = random.Random(371)
    # m=1 shape: k=4 (boundary = ceiling)
    for p in (12289, 65537):
        run_block(4, [5, 6, 7, 8],
                  [("KKH26 [x^5,x^4]", (5, 4)), ("worst [x^7,x^6]", (7, 6)),
                   ("worst [x^5,x^12]", (5, 12)),
                   ("far-generic #0", 'random'), ("far-generic #1", 'random'),
                   ("far-generic #2", 'random')], p, rng)
    # m=2 shape: k=3 (mu=3, m=2, r=3: KKH26 line = [x^6, x^4], ceiling band a = 6)
    for p in (12289, 65537):
        run_block(3, [4, 5, 6, 7, 8],
                  [("KKH26 [x^6,x^4]", (6, 4)), ("shift [x^7,x^5]", (7, 5)),
                   ("hifreq [x^7,x^6]", (7, 6)), ("hifreq [x^9,x^7]", (9, 7)),
                   ("far-generic #0", 'random'), ("far-generic #1", 'random'),
                   ("far-generic #2", 'random')], p, rng)
    print("\nReading: k=3 block = the m=2 (deep-ceiling) shape; the KKH26 line should")
    print("show alignable 6-sets (squaring-map fibre unions). Extremality at a=6 is")
    print("the deployed-extremizer question at the smallest honest scale.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
