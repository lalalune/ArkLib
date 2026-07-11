#!/usr/bin/env python3
"""
probe_407_orbit_count_thinness.py  (#407) -- FAST subset-driven version

RULE-3 TEST on the ORBIT-COUNT lever (brick 5 / OrbitCountCrossingLaw).

Crossing law (axiom-clean, in-tree): I_pencil(delta) <= n  <=>  N_pencil(delta) <= gcd(b-a,n),
N_pencil = #orbits of bad-alpha set under alpha -> alpha*omega^{b-a}.
OPEN: does N_pencil stay bounded (O(1)) at constant rate in the small-gap window?

QUESTION (rule-3, nobody ran on the orbit object): is max-over-pencils N THINNESS-ESSENTIAL?
  thick maxN > thin maxN  => thinness-essential signal (live edge)
  thick maxN == thin maxN => THICKNESS-INVARIANT => rule-3-incompatible lever (mapped wall)

FAST METHOD (exact, no per-alpha scan over F_q):
A bad alpha at agreement threshold t means: exists a t-subset A of mu_n and a deg<k poly g with
  g(x) = x^a + alpha*x^b  for all x in A.
For |A| = t >= k+1 the subset is OVER-DETERMINED. Fix alpha as unknown; the condition "the t points
(x, x^a+alpha x^b) lie on a deg<k poly" is: all order-k divided differences over A vanish. Each such
DD is LINEAR (actually affine) in alpha:  DD = DD0 + alpha*DD1. So the bad alphas contributed by a
given subset A are the COMMON roots of {DD0_j + alpha*DD1_j = 0}_j over the (t-k) windows:
  - if some DD1_j != 0: unique alpha = -DD0_j/DD1_j, valid iff it satisfies ALL windows (and gives
    agreement >= t after recheck).
  - if all DD1_j == 0 and all DD0_j == 0: alpha free (degenerate near-direction) -- skip (saturating).
So per subset we get at most ONE candidate alpha. Union over all C(n,t) subsets = full bad set.
This is exact and avoids the O(q) scan. For t = n-1 there are only n subsets; for t=n-2, C(n,2).
"""
from math import gcd, log
import itertools


def is_prime(x):
    if x < 2:
        return False
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if x % p == 0:
            return x == p
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        y = pow(a, d, x)
        if y == 1 or y == x - 1:
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def find_omega(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) != 1:
            continue
        if all(not (n % d == 0 and pow(cand, d, q) == 1) for d in range(1, n)):
            return cand
    return None


def primes_for(n, betas):
    out = []
    for beta in betas:
        target = int(round(n ** beta))
        found = None
        for delta in range(0, 8 * n * n + 1):
            for cand in (target + delta, target - delta):
                if cand > n and (cand - 1) % n == 0 and is_prime(cand):
                    found = (cand, log(cand) / log(n))
                    break
            if found:
                break
        if found:
            out.append(found)
    return out


def dd_k(xs, ys, k, q):
    """order-k divided difference of (xs,ys) over k+1 nodes (len == k+1)."""
    v = list(ys)
    for j in range(1, k + 1):
        for i in range(k, j - 1, -1):
            inv = pow((xs[i] - xs[i - j]) % q, q - 2, q)
            v[i] = ((v[i] - v[i - 1]) * inv) % q
    return v[k]


def bad_alphas_for_pencil(D, a, b, k, q, t):
    """exact bad-alpha set at agreement threshold t for pencil (a,b), via subset-driven solve.
    Returns set of alpha in F_q that achieve agreement >= t with some deg<k poly."""
    n = len(D)
    # precompute u0[i] = x_i^a, u1[i] = x_i^b
    u0 = [pow(x, a, q) for x in D]
    u1 = [pow(x, b, q) for x in D]
    bad = set()
    for sub in itertools.combinations(range(n), t):
        xs = [D[i] for i in sub]
        if len(set(xs)) < t:
            continue
        v0 = [u0[i] for i in sub]
        v1 = [u1[i] for i in sub]
        # windows of size k+1; collect (DD0,DD1) linear-in-alpha constraints
        cand_alpha = None
        free = True
        ok = True
        for st in range(t - k):
            w_xs = xs[st:st + k + 1]
            d0 = dd_k(w_xs, v0[st:st + k + 1], k, q)
            d1 = dd_k(w_xs, v1[st:st + k + 1], k, q)
            if d1 % q != 0:
                sol = (-d0 * pow(d1, q - 2, q)) % q
                if cand_alpha is None:
                    cand_alpha = sol
                    free = False
                elif cand_alpha != sol:
                    ok = False
                    break
            else:
                if d0 % q != 0:
                    ok = False  # 0 + alpha*0 = d0 != 0, no solution
                    break
                # 0=0, no constraint from this window
        if not ok:
            continue
        if free:
            # all windows degenerate (saturating subset) -> alpha free; skip (not a finite bad alpha)
            continue
        # cand_alpha satisfies ALL (t-k) consecutive order-k DD windows == 0 over this t-subset.
        # That is EXACTLY the condition that the t points (x, x^a+alpha x^b), x in subset, lie on a
        # single deg<k poly => agreement >= t by construction. No recheck needed (it was redundant).
        bad.add(cand_alpha)
    return bad


def max_agreement_quick(D, ys, k, q):
    """max #points on a single deg<k poly. Uses k-subset interpolation but only when needed."""
    n = len(D)
    if k >= n:
        return n
    best = 0
    for sub in itertools.combinations(range(n), k):
        xs = [D[i] for i in sub]
        if len(set(xs)) < k:
            continue
        coeffs = lagrange_coeffs(xs, [ys[i] for i in sub], q)
        cnt = sum(1 for i in range(n) if poly_eval(coeffs, D[i], q) == ys[i])
        if cnt > best:
            best = cnt
        if best == n:
            break
    return best


def lagrange_coeffs(xs, vs, q):
    k = len(xs)
    poly = [0] * k
    for i in range(k):
        num = [1]
        denom = 1
        for j in range(k):
            if j == i:
                continue
            num = poly_mul(num, [(-xs[j]) % q, 1], q)
            denom = (denom * (xs[i] - xs[j])) % q
        scale = (vs[i] * pow(denom, q - 2, q)) % q
        for t in range(len(num)):
            poly[t] = (poly[t] + num[t] * scale) % q
    return poly


def poly_mul(a, b, q):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            res[i + j] = (res[i + j] + ai * bj) % q
    return res


def poly_eval(coeffs, x, q):
    r = 0
    p = 1
    for c in coeffs:
        r = (r + c * p) % q
        p = p * x % q
    return r


def count_orbits(S_set, mult, q):
    seen = set()
    orbits = 0
    for a in S_set:
        if a in seen:
            continue
        orbits += 1
        b = a
        while True:
            seen.add(b)
            b = b * mult % q
            if b == a:
                break
            if b not in S_set:
                break
    return orbits


def maxN(q, n, k, omega, thr):
    D = [pow(omega, i, q) for i in range(n)]
    mN = mI = 0
    arg = None
    cross_ok = eq_ok = True
    for a in range(k, n):
        for b in range(a + 1, n + 1):
            db = (b - a) % n
            if db == 0:
                db = n
            d = gcd(db, n)
            S = n // d
            mult = pow(omega, (b - a) % n, q)
            bad = bad_alphas_for_pencil(D, a, b, k, q, thr)
            if not bad:
                continue
            I = len(bad)
            N = count_orbits(bad, mult, q)
            if I != N * S:
                eq_ok = False
            if (I <= n) != (N <= d):
                cross_ok = False
            if N > mN:
                mN = N
                arg = (a, b, d, S, I)
            if I > mI:
                mI = I
    return mN, mI, arg, cross_ok, eq_ok


def main():
    print("# ORBIT-COUNT THINNESS-ESSENTIALITY (rule-3 test, brick 5 / OrbitCountCrossingLaw)")
    print("# max-over-far-pencils orbit count N at binding threshold; thick vs thin per n.")
    print("# FAST subset-driven exact solve (no O(q) alpha scan).\n")
    # thr sweep through the BINDING band: for n=8,k=2 delta* ~ 0.6-0.8 => thr ~ 2-4;
    # for n=16,k=4 delta*=9/16 => thr ~ 7. Sweep a band around k+1 .. n//2+1.
    import os
    only8 = os.environ.get('ONLY8') == '1'
    configs = [
        (8, 2, [2.0, 2.5, 3.0, 4.0, 4.5], list(range(3, 7))),
    ]
    if not only8:
        configs.append((16, 4, [2.0, 2.5, 3.0, 4.0], list(range(5, 11))))
    for (n, k, betas, thrs) in configs:
        print(f"=== n={n} k={k} rho={k/n:.3f} (Johnson {1-(k/n)**0.5:.3f}) ===")
        primes = primes_for(n, betas)
        for thr in thrs:
            print(f"  -- threshold >= {thr} (delta={(n-thr)/n:.3f}) --")
            row = []
            for (q, beta) in primes:
                omega = find_omega(q, n)
                if omega is None:
                    continue
                mN, mI, arg, cok, eok = maxN(q, n, k, omega, thr)
                tag = "THIN" if beta >= 3.5 else ("thick" if beta < 2.7 else "mid")
                print(f"    p={q:>9} beta={beta:.2f} [{tag:5}]: maxN={mN:>3} maxI={mI:>4} "
                      f"arg(a,b,d,S,I)={arg} crossOK={cok} factOK={eok}", flush=True)
                row.append((beta, mN, mI, tag))
            thinNs = [r[1] for r in row if r[3] == "THIN"]
            thickNs = [r[1] for r in row if r[3] == "thick"]
            if thinNs and thickNs:
                tn, tk = max(thinNs), max(thickNs)
                if tk > tn:
                    v = f"thick maxN={tk} > thin maxN={tn} => THINNESS-ESSENTIAL signal (live edge)"
                elif tk == tn:
                    v = f"thick maxN={tk} == thin maxN={tn} => THICKNESS-INVARIANT (rule-3-incompat, mapped wall)"
                else:
                    v = f"thick maxN={tk} < thin maxN={tn} => larger in THIN (anti-thinness)"
                print(f"    VERDICT(thr={thr}): {v}")
        print()


if __name__ == "__main__":
    main()
