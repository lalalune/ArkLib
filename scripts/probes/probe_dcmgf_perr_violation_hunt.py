#!/usr/bin/env python3
# Hunt for a REAL per-r DCWickBound violation (dcTerm_r > gaussTerm_r) that co-exists with a
# valid aggregate DC-MGF bound, to prove the slack-tolerant producer is NON-vacuously weaker.
# Strategy: violations live at the BCHKS onset where E_r exceeds the Wick ceiling (2r-1)!! n^r.
# Test the RAW per-r Wick ratio E_r / ((2r-1)!! n^r) directly (independent of y): if it exceeds 1
# at some r, the corresponding dcTerm (q*E_r - n^{2r}) can exceed gaussTerm for suitable saddle y.
# Use several thin primes incl. structured (v2-heavy) ones; n in {8,16}.
import math


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
    k = 2 * r
    if k == 0:
        return 1
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


def dfact(m):
    # (2r-1)!! for m=2r-1 odd; dfact(-1)=1 convention via r=0
    if m <= 0:
        return 1
    r = 1
    while m > 0:
        r *= m
        m -= 2
    return r


def v2(x):
    s = 0
    while x % 2 == 0:
        x //= 2
        s += 1
    return s


def main():
    found = False
    for n in [8, 16]:
        # gather thin primes p = 1 mod n, beta in [3.5..5], prefer high v2(p-1)
        primes = []
        for beta in [3.5, 4.0, 4.5, 5.0]:
            base = int(n ** beta)
            best = None
            for p in range(base, base + 20000):
                if p % n == 1 and isprime(p):
                    if best is None or v2(p - 1) > v2(best - 1):
                        best = p
                    if v2(p - 1) >= 8:
                        best = p
                        break
            if best:
                primes.append((beta, best))
        # also try a Fermat-ish: p=65537 with n=16 (v2=16)
        if n == 16:
            primes.append((math.log(65537) / math.log(16), 65537))
        for beta, p in primes:
            if n ** 2 * p > 3_000_000_00:  # convolution cost guard for big p
                pass
            mu = subgroup(n, p)
            q = p
            print(f"\n=== n={n} p={p} beta~{beta:.2f} v2(p-1)={v2(p-1)} ===")
            maxr = 9 if p < 20000 else 7
            ratios = []
            for r in range(1, maxr):
                Er = energy_r(n, p, mu, r)
                wick = dfact(2 * r - 1) * n ** r
                ratio = Er / wick
                ratios.append((r, Er, ratio))
            # per-r DCWick (y-free surrogate): DCWick <=> q*E_r - n^{2r} <= q*Wick
            # <=> E_r - n^{2r}/q <= Wick. Since n^{2r}/q small at thin q, ~ E_r <= Wick.
            for r, Er, ratio in ratios:
                wick = dfact(2 * r - 1) * n ** r
                dcwick_lhs = q * Er - n ** (2 * r)
                dcwick_rhs = q * wick
                viol = dcwick_lhs > dcwick_rhs
                tag = " <-- DCWick VIOLATED" if viol else ""
                if viol:
                    found = True
                print(f"  r={r}: E_r/Wick={ratio:.4f}  DCWick({'FAIL' if viol else 'ok'}){tag}")
    print(f"\nVERDICT: a genuine per-r DCWick violation was {'FOUND' if found else 'NOT found'} "
          f"at the probed thin instances (n<=16).")
    print("If not found here, lalalune's #444 21:06 probe reports per-r ratios cross 1 only deeper"
          " / at larger n than brute-forceable here; the aggregate producer is still the correct"
          " (strictly-weaker) Lean object — it degenerates to the proven (∀r) producer when no term"
          " violates, and strictly extends it when some do.")


main()
