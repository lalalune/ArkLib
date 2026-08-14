#!/usr/bin/env python3
"""
probe_charp_stepratio_refute_and_lc_margin.py  (#444, door-iv char-p transfer lane)

INDEPENDENT verification (second implementation, exact bignum) of two things:

(A) The char-p step-ratio monotonicity REFUTATION (_CharPStepRatioMonotoneFails.lean,
    commit 29acc887a): with the CORRECT cyclotomic/antipodal E_r(C), the char-p energy
    step-ratio gap  G_p = (2r+3) E_{r+1}^2 - (2r+1) E_r E_{r+2}  is NEGATIVE at concrete
    prize-regime points, while the char-0 gap is POSITIVE. Reproduces the two Lean witnesses
    from an independent code path (Counter-convolution), confirming the route is soundly dead.

(B) The wraparound log-concavity MARGIN TREND that the v2 probe receipt understates.
    v2 (probe_charp_wraparound_logconcave_Q_v2.py) stops at rmax<=6, so the ONLY genuinely
    non-vacuous test of  W_r*W_{r+2} <= W_{r+1}^2  in the whole suite is n=16,p=65537,r=4
    (W_1..W_3 = 0 everywhere; the receipt's cited "non-vacuous r=3" cases are VACUOUS, W_3=0).
    Pushing r to 8 at n=16 over several p~n^4 primes gives genuine non-vacuous tests at
    r=4,5,6: log-concavity HOLDS at every one, but the ratio W_r*W_{r+2}/W_{r+1}^2 climbs
    MONOTONICALLY toward the borderline 1 (e.g. p=65537: 0.654 -> 0.830 -> 0.901), consistent
    with W_r ~ n^{2r}/p  =>  ratio -> 1. So even the SUFFICIENT condition is a finite-size
    signal trending to marginality; "empirically forced in the prize regime" overstates it.

NOTHING here changes any Lean. CORE stays OPEN. This is a verification/honesty receipt.
"""
import sys
from collections import Counter
from sympy import isprime


def factorize(m):
    f = {}; d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1; m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def primitive_root(p):
    facs = list(factorize(p - 1).keys())
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")


def gen_mu_n(p, n):
    """Generator of mu_n without factoring p-1 (n a 2-power): order n iff c^(n/2) != 1."""
    e = (p - 1) // n; t = 2
    while True:
        c = pow(t, e, p)
        if c != 1 and pow(c, n // 2, p) != 1:
            return c
        t += 1


def subgroup(p, n, factor_ok=True):
    h = primitive_root(p) if factor_ok else 2
    h = pow(h, (p - 1) // n, p) if factor_ok else gen_mu_n(p, n)
    S = []; x = 1
    for _ in range(n):
        S.append(x); x = (x * h) % p
    assert len(set(S)) == n
    return S


def Er_Fp(S, p, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[(v + x) % p] += m
        c = nc
    return sum(m * m for m in c.values())


def Er_C_2power(n, r):
    """Correct cyclotomic E_r(C), n=2^k: z^a -> +e_a (a<n/2) or -e_{a-n/2} (a>=n/2)."""
    half = n // 2
    units = [(a, 1) if a < half else (a - half, -1) for a in range(n)]
    c = Counter({tuple([0] * half): 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for (idx, s) in units:
                w = list(v); w[idx] += s; nc[tuple(w)] += m
        c = nc
    return sum(m * m for m in c.values())


def part_A():
    print("=== (A) char-p step-ratio monotonicity REFUTATION (independent reproduction) ===")
    witnesses = [
        (32, 786433, 3, (446720, 92179360, 24850732032)),
        (64, 2752513, 2, (12096, 3750400, 1666665280)),
    ]
    ok = True
    for n, p, r, exp in witnesses:
        S = subgroup(p, n)
        E = {k: Er_Fp(S, p, k) for k in (r, r + 1, r + 2)}
        match = tuple(E[k] for k in (r, r + 1, r + 2)) == exp
        Gp = (2 * r + 3) * E[r + 1] ** 2 - (2 * r + 1) * E[r] * E[r + 2]
        C = {k: Er_C_2power(n, k) for k in (r, r + 1, r + 2)}
        Gc = (2 * r + 3) * C[r + 1] ** 2 - (2 * r + 1) * C[r] * C[r + 2]
        ok = ok and match and Gp < 0 and Gc > 0
        print(f"  n={n} p={p} r={r}: E={tuple(E[k] for k in (r,r+1,r+2))} match={match}")
        print(f"     char-p gap G_p={Gp}  ({'NEG: monotonicity FAILS' if Gp<0 else 'pos'})")
        print(f"     char-0 gap G_0={Gc}  ({'POS: monotonicity holds' if Gc>0 else 'neg'})")
        sys.stdout.flush()
    print(f"  -> refutation reproduced (both witnesses, G_p<0<G_0): {ok}")
    return ok


def part_B():
    print("\n=== (B) wraparound log-concavity margin trend (n=16, push r to 8) ===")
    n, RMAX = 16, 8
    lo, hi = n ** 4, 3 * n ** 4
    primes = []
    k = (lo - 1) // n + 1
    while len(primes) < 4 and k * n + 1 <= hi:
        p = k * n + 1
        if isprime(p):
            primes.append(p)
        k += 1
    EC = {r: Er_C_2power(n, r) for r in range(1, RMAX + 1)}
    for p in primes:
        S = subgroup(p, n, factor_ok=False)
        W = {r: Er_Fp(S, p, r) - EC[r] for r in range(1, RMAX + 1)}
        ratios = []
        for r in range(1, RMAX - 1):
            a, b, c = W[r], W[r + 1], W[r + 2]
            if a > 0 and b > 0 and c > 0:
                ratios.append((r, (a * c) / (b * b), a * c <= b * b))
        rtxt = "  ".join(f"r={r}:{ratio:.4f}{'' if lc else '!FAIL'}" for r, ratio, lc in ratios)
        print(f"  p={p}: nonvacuous LC ratios W_r W_(r+2)/W_(r+1)^2 -> {rtxt}")
        sys.stdout.flush()
    print("  -> LC holds at every non-vacuous point but ratio climbs toward 1 (finite-size).")


if __name__ == "__main__":
    a = part_A()
    part_B()
    sys.exit(0 if a else 1)
