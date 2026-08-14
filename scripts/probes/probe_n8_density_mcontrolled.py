#!/usr/bin/env python3
"""
ANGLE [N8] DENSITY, m-CONTROLLED (#444). Follow-up to probe_n8_floor_violator_density.py.

The first density probe found denA (SHARP-floor violator density) RISING with n (0,0,.005,.035 at
n=8,16,32,64) -- but the beta-window COLLAPSED (m-cap forced p near n^3.6, so m shrank with n).
A rising denA could therefore be an m-collapse ARTIFACT: smaller m = fewer cosets = less averaging
=> M/sqrt(2n ln m) inflates mechanically, NOT a genuine more-structured-primes effect.

THIS PROBE disentangles by holding the COSET COUNT m in a FIXED band [m_lo, m_hi] across all n
(so the sharp floor's ln m is comparable), and sampling ALL primes p == 1 mod n with m in that band.
Then the SHARP-floor violator density is measured as a function of n at COMPARABLE m.

ALSO: a separate "STRUCTURED vs GENERIC" split. For each n we partition the in-band primes by
v2(p-1) (2-adic depth of the field):
  - GENERIC bucket: v2(p-1) == mu  (the minimal 2-part, mu_n is the FULL 2-Sylow)
  - STRUCTURED bucket: v2(p-1) >= mu + 3 (field has a much bigger 2-group than mu_n; Fermat-like)
and report the violator density in EACH bucket. The N8 question is whether the STRUCTURED bucket
has a density bounded away from 0 (=> infinitely many violators at every scale => universal-over-F
sharp law false) while the GENERIC bucket -> 0.

RIGOR NOTE: M is exact (max over m coset reps of |sum cos|, float err << 1). m fixed-band controls
the floor denominator. v2-split isolates the structured effect cleanly.
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

def in_band_primes(n, m_lo, m_hi, cap):
    """all primes p = m*n+1 with m in [m_lo, m_hi]. p==1 mod n automatic. proper subgroup m>=2."""
    out = []
    for m in range(max(2, m_lo), m_hi + 1):
        p = m * n + 1
        if isprime(p):
            out.append((p, m))
        if len(out) >= cap: break
    return out

def run(n, m_lo, m_hi, cap):
    mu = int(round(math.log2(n)))
    prs = in_band_primes(n, m_lo, m_hi, cap)
    if not prs: return None
    gen = []; struc = []; allr = []
    for (p, m) in prs:
        M = Mmax(p, n, m)
        fA = math.sqrt(2 * n * math.log(m))
        fB = 2 * math.sqrt(n * math.log(p))
        rec = (p, m, M, M / fA, M / fB, v2(p - 1))
        allr.append(rec)
        if v2(p - 1) == mu: gen.append(rec)
        elif v2(p - 1) >= mu + 3: struc.append(rec)
    def dens(bucket):
        if not bucket: return (0, 0.0, 0.0)
        nv = sum(1 for r in bucket if r[3] > 1.0)
        return (len(bucket), nv / len(bucket), max(r[3] for r in bucket))
    return dict(n=n, mu=mu, nall=len(allr), beta=math.log(prs[len(prs)//2][0])/math.log(n),
                gen=dens(gen), struc=dens(struc), allb=dens(allr),
                betalo=math.log(prs[0][0])/math.log(n), betahi=math.log(prs[-1][0])/math.log(n))

if __name__ == "__main__":
    print("=" * 105)
    print("N8 m-CONTROLLED density: coset-count m held in FIXED band across n, SHARP-floor violator density.")
    print("buckets: GENERIC v2(p-1)=mu (mu_n = full 2-Sylow); STRUCTURED v2(p-1)>=mu+3 (Fermat-like field).")
    print("=" * 105)
    # fixed m band: m in [256, 1024] so ln m ~ 6-7 comparable across all n. p = m*n+1.
    M_LO, M_HI = 256, 4096
    print(f"  (coset-count band m in [{M_LO},{M_HI}]; beta=log_n p drifts but m -- the floor's ln m -- is FIXED)")
    print(f"{'n':>5} {'beta-win':>14} {'#all':>5} | {'gen:#':>6} {'genDen':>7} {'genWorst':>8} | {'str:#':>6} {'strDen':>7} {'strWorst':>8} | {'allDen':>7}")
    for mu in range(3, 9):
        n = 1 << mu
        res = run(n, M_LO, M_HI, cap=350)
        if res is None:
            print(f"{n:>5}  (none)"); continue
        g = res['gen']; s = res['struc']; a = res['allb']
        print(f"{n:>5} b[{res['betalo']:.2f},{res['betahi']:.2f}] {res['nall']:>5} | "
              f"{g[0]:>6} {g[1]:>7.3f} {g[2]:>8.4f} | "
              f"{s[0]:>6} {s[1]:>7.3f} {s[2]:>8.4f} | {a[1]:>7.3f}")
        sys.stdout.flush()
    print()
    print("READING: with m (=> floor denominator) FIXED across n, compare genDen vs strDen trends.")
    print(" If strDen stays BOUNDED-AWAY-FROM-0 (or rises) while genDen ~ 0  => structured/Fermat-like fields")
    print("   carry a PERSISTENT positive density of SHARP-floor violators => universal-over-F sharp law FALSE.")
    print(" If BOTH -> 0 with n at fixed m => the n=64 rise in the first probe was the m-collapse artifact,")
    print("   sharp-floor violation is measure-zero, negative closure FAILS (absorbed by constant).")
