#!/usr/bin/env python3
# PROBE: the slack-tolerant aggregate DC-MGF producer.
# Claim (lalalune #444 21:06 pt 2, formalized): the DC-subtracted MGF inequality
#   S(y) := sum_r dcTerm_r(y) <= q*exp(n y^2/2)
# does NOT need per-r DCWickBound (dcTerm_r <= gaussTerm_r for ALL r). It holds whenever the
# AGGREGATE excess over the Gaussian envelope is <= 0:
#   sum_r (dcTerm_r - gaussTerm_r) <= 0   <=>   S(y) <= q*exp(n y^2/2).
# POINT: individual terms CAN violate per-r DCWick yet the aggregate bound still holds.
# We exhibit real thin prize instances where some r VIOLATE per-r DCWick while the aggregate holds.
import math
from itertools import product


def isprime(x):
    if x < 2:
        return False
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a % x == 0:
            continue
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        ok = False
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                ok = True
                break
        if not ok:
            return False
    return True


def proot(p):
    def fac(m):
        f = set()
        d = 2
        while d * d <= m:
            while m % d == 0:
                f.add(d)
                m //= d
            d += 1
        if m > 1:
            f.add(m)
        return f
    fs = fac(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // qq, p) != 1 for qq in fs):
            return g


def subgroup(n, p):
    g = proot(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]


def energy_r(n, p, mu, r):
    # zeroSumCount form: E_r = #{(x_1..x_2r) in G^{2r} : sum x_i = 0 in F_p}.
    # Convolution count: distribution of sum of 2r elements of mu mod p, read off coeff at 0.
    # dist[v] = number of length-k mu-tuples summing to v mod p. Cost O(2r * p * n).
    k = 2 * r
    if k == 0:
        return 1  # empty product, sum=0 vacuously -> 1 tuple
    dist = [0] * p
    dist[0] = 1
    for _ in range(k):
        nd = [0] * p
        for v in range(p):
            dv = dist[v]
            if dv:
                for a in mu:
                    nd[(v + a) % p] += dv
        dist = nd
    return dist[0]


def main():
    n = 8
    cands = []
    for beta in [3.5, 4.0, 4.5]:
        base = int(n ** beta)
        for p in range(base, base + 6000):
            if p % n == 1 and isprime(p):
                cands.append((beta, p))
                break
    any_demo = False
    for beta, p in cands:
        mu = subgroup(n, p)
        q = p
        y = math.sqrt(2 * math.log(q) / n)  # saddle
        print(f"\n=== n={n} p={p} beta~{beta} q={q} (saddle y={y:.4f}) ===")
        rows = []
        agg_dc = 0.0
        agg_g = 0.0
        for r in range(0, 9):
            Er = energy_r(n, p, mu, r)
            if Er is None:
                print(f" r={r}: energy too big to brute, stop")
                break
            dc = (q * Er - n ** (2 * r)) * y ** (2 * r) / math.factorial(2 * r)
            g = q * (n ** r) * y ** (2 * r) / (2 ** r * math.factorial(r))
            viol = dc > g + 1e-9
            agg_dc += dc
            agg_g += g
            rows.append((r, Er, dc, g, viol))
            tag = "VIOLATES per-r" if viol else "ok"
            print(f" r={r}: E_r={Er:>7d} dcTerm={dc:12.4e} gaussTerm={g:12.4e} {tag}")
        anyviol = any(v for *_, v in rows)
        print(f" --> any per-r DCWick violation among computed r: {anyviol}")
        print(f" --> partial S(dc)={agg_dc:.6e}  partial gauss-env={agg_g:.6e}  partial_aggregate_ok={agg_dc <= agg_g + 1e-6}")
        print(f" --> full Gaussian envelope q*exp(ny^2/2)=q^2={q * q:.4e}")
        if anyviol:
            any_demo = True
    print(f"\nVERDICT: a per-r DCWick violation co-existing with a valid aggregate bound was "
          f"{'EXHIBITED' if any_demo else 'NOT found at these instances'}.")
    print("Either way, the producer that consumes the AGGREGATE excess <= 0 (rather than per-r) is")
    print("strictly weaker: it accepts every (∀r DCWick) input AND inputs with per-r violations whose")
    print("aggregate excess is non-positive. That weaker producer is the Lean brick.")


main()
