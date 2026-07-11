#!/usr/bin/env python3
"""
ANGLE [N8] DECISIVE: SHARP-floor violator density as a function of the COSET COUNT m (#444).

The two prior probes revealed the controlling variable is m = (p-1)/n (the coset count / relative
subgroup size), NOT raw n:
  - fixed SMALL m-band [256,4096], n=64..256: SHARP-floor violator density ~ 8-19% (structured higher)
  - TRUE prize regime n=64, beta=4 (m ~ 262144): density only 3.3%, worst R=1.051, median 0.906

The PRIZE asymptotic is n=2^30, beta=4-5  =>  m = (p-1)/n ~ n^{beta-1} ~ 2^90  (HUGE m).
So the decisive question is: does the SHARP-floor (sqrt(2) constant) violator density DECAY as m
grows (=> measure-zero at prize scale, sharp law a.e.-true, the n=64-small-m rise was a small-m
artifact) or stay BOUNDED AWAY FROM 0 as m -> infinity (=> persistent positive density => universal
sharp law false even at prize scale)?

DESIGN: fix n (32 and 64, where exact M over m cosets is computable to m ~ 2^17). Sweep m across
octaves [2^k, 2^{k+1}) for k = 8..16. In each octave sample many primes p = m*n+1 (p==1 mod n,
proper subgroup). Measure:
  - density of SHARP-floor violators (M > sqrt(2n ln m))
  - density of ABSORB-floor violators (M > 2 sqrt(n ln p))  [the surviving prize-relevant bound]
  - worst R_sharp and worst R_absorb in the octave
  - the same split by 2-adic depth (structured v2>=mu+3 vs generic v2==mu)

If R_sharp violator density vs log2(m) is DECREASING (extrapolating to ~0 by m=2^90), the negative
closure on the sharp law FAILS asymptotically (small-m artifact). If FLAT/INCREASING, it is a
genuine persistent obstruction. The ABSORB density is the prize-relevant survivor; 0 there = no
prize-falsifying violators at all.

RIGOR: exact M (max over m cosets); density over a real prime sample in each octave; trend in m is
the load-bearing extrapolation toward the prize m ~ 2^90 (stated as an EXTRAPOLATION, not a proof).
"""
import math, sys
from sympy import isprime, primitive_root

def v2(x):
    s = 0
    while x % 2 == 0: x //= 2; s += 1
    return s

def Mmax(p, n, m):
    g = primitive_root(p)
    h = pow(g, m, p)
    mun = [pow(h, j, p) for j in range(n)]
    w = 2 * math.pi / p
    M = 0.0
    for j in range(m):
        b = pow(g, j, p)
        s = 0.0
        for x in mun:
            s += math.cos(w * ((b * x) % p))
        a = abs(s)
        if a > M: M = a
    return M

def octave_sample(n, m_lo, m_hi, want):
    """sample up to `want` primes p=m*n+1, m in [m_lo,m_hi)."""
    out = []
    span = m_hi - m_lo
    # stride to spread across the octave
    stride = max(1, span // (want * 3))
    m = m_lo
    while m < m_hi and len(out) < want:
        p = m * n + 1
        if isprime(p):
            out.append((p, m))
        m += stride
    return out

def run_octave(n, k, want):
    mu = int(round(math.log2(n)))
    m_lo, m_hi = 1 << k, 1 << (k + 1)
    prs = octave_sample(n, m_lo, m_hi, want)
    if not prs: return None
    allr = []; gen = []; struc = []
    for (p, m) in prs:
        M = Mmax(p, n, m)
        rS = M / math.sqrt(2 * n * math.log(m))
        rA = M / (2 * math.sqrt(n * math.log(p)))
        rec = (rS, rA, v2(p - 1))
        allr.append(rec)
        if v2(p - 1) == mu: gen.append(rec)
        elif v2(p - 1) >= mu + 3: struc.append(rec)
    def D(b):
        if not b: return (0, 0.0, 0.0, 0.0)
        return (len(b), sum(1 for r in b if r[0] > 1)/len(b),
                max(r[0] for r in b), max(r[1] for r in b))
    return dict(n=n, k=k, allb=D(allr), gen=D(gen), struc=D(struc))

if __name__ == "__main__":
    print("=" * 100)
    print("N8 DECISIVE: SHARP-floor violator density vs coset-count m (octaves). Prize m ~ 2^90.")
    print("denS = frac M>sqrt(2n ln m) [sharp sqrt2]; denA = frac M>2sqrt(n ln p) [absorb, survivor].")
    print("=" * 100)
    for n in [32, 64]:
        print(f"\n--- n = {n} (mu={int(round(math.log2(n)))}) ---")
        print(f"{'log2 m':>7} {'#pr':>4} {'denS':>6} {'worstS':>7} {'worstA':>13} | "
              f"{'gen denS':>8} {'gen wS':>7} | {'str denS':>8} {'str wS':>7}")
        for k in range(8, 17):
            want = 60 if k <= 13 else 24
            res = run_octave(n, k, want)
            if res is None:
                print(f"{k:>7}  (none)"); continue
            a = res['allb']; g = res['gen']; s = res['struc']
            # a = (count, denS, worstS, worstA)
            print(f"{k:>7} {a[0]:>4} {a[1]:>6.3f} {a[2]:>7.4f} {a[3]:>6.4f}{'':>7} | "
                  f"{g[1]:>8.3f} {g[2]:>7.4f} | {s[1]:>8.3f} {s[2]:>7.4f}")
            sys.stdout.flush()
    print()
    print("READING: track denS vs log2 m. If denS DECAYS toward 0 as log2 m grows (-> prize m=2^90),")
    print(" the sharp-floor violation is a SMALL-m artifact (a.e.-true asymptotically), negative closure FAILS.")
    print(" If denS is FLAT/RISING in log2 m, structured primes carry a PERSISTENT positive violator density")
    print(" => universal-over-F sharp sqrt(2) law is FALSE even at prize scale (but absorb-floor still governs).")
    print(" denA (absorb survivor): if ==0 throughout, NO prize-falsifying violators exist at any m.")
