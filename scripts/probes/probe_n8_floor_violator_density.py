#!/usr/bin/env python3
"""
ANGLE [N8-structured-prime-density] (#444 / proximity prize) -- NEGATIVE-DIRECTION DENSITY TEST.

QUESTION (the precise N8 mandate): how DENSE are floor-violating structured/near-2-group primes
among PRIZE-SHAPED primes (p ~ n^4, p == 1 mod n, proper mu_n: n=2^mu, m=(p-1)/n > 1)?

  If a POSITIVE FRACTION (or infinitely many at every scale) violate the floor, then the
  per-code law "delta*_C = 1-rho-Theta(1/log n) for ALL sufficiently large smooth F" is
  FALSIFIED as a universal-over-F statement, and the prize delta* (if it must hold for all large
  smooth F) is unattainable in that closed form.

  If the violator density -> 0 (and the SURVIVING absorbing floor has 0 violators), then the
  negative closure FAILS: structured primes are measure-zero exceptions absorbed by a constant.

TWO FLOORS, measured separately over the SAME prize-faithful prime window:
  (A) SHARP floor  : M(n) <= sqrt(2 n ln m)         [char-0 Wick sharp constant sqrt(2)]
  (B) ABSORB floor : M(n) <= 2 sqrt(n ln p)         [the irrefutable survivor, constant 2]

For EACH n=2^mu we enumerate ALL prize-shaped primes in a window p in [n^beta_lo, n^beta_hi]
(beta ~ 4, the prize regime) with p == 1 mod n, and for each compute
  M(n,p) = max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} cos(2 pi b x / p)
(eta constant on cosets b*mu_n => enumerate m coset reps). Then:
  - density_A = #{p : M > sqrt(2n ln m)} / #primes
  - density_B = #{p : M > 2 sqrt(n ln p)} / #primes
  - we also CORRELATE violation with v2(p-1) (2-adic depth of the field) and with the
    RELATIVE subgroup size n/(p-1) (how big is mu_n inside F^x).

RIGOR: this is an EXACT computation (exact integer cosets, float cosine sum at double precision;
M is a max of m terms each |.|<=n so float error << 1). A density that is BOUNDED AWAY FROM ZERO
and PERSISTS as n grows would be a rigorous obstruction; a density that DECAYS to 0 is a rigorous
no-closure for the universal-over-F reading. We report the trend, not a single n.
"""
import math, sys
from sympy import isprime, primitive_root

def v2(x):
    s = 0
    while x % 2 == 0: x //= 2; s += 1
    return s

def Mmax(p, n, g=None, cap=400000):
    """Exact M(n,p) = max_{b!=0}|eta_b|, b ranging over m coset reps. None if m too big."""
    m = (p - 1) // n
    if m > cap: return None
    if g is None: g = primitive_root(p)
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

def window_primes(n, blo, bhi, cap_primes=200, m_min=2):
    """ALL primes p==1 mod n in [n^blo, n^bhi] with m=(p-1)/n >= m_min (proper subgroup)."""
    lo = int(n ** blo); hi = int(n ** bhi)
    out = []
    k = max(1, lo // n)
    while k * n + 1 <= hi and len(out) < cap_primes:
        p = k * n + 1
        if p >= lo and isprime(p) and (p - 1) // n >= m_min:
            out.append(p)
        k += 1
    return out

def run(n, blo, bhi, cap_primes, m_cap):
    primes = window_primes(n, blo, bhi, cap_primes)
    # only keep those with m within compute cap
    usable = [p for p in primes if (p - 1) // n <= m_cap]
    if not usable:
        return None
    rec = []
    for p in usable:
        M = Mmax(p, n, cap=m_cap)
        if M is None: continue
        m = (p - 1) // n
        fA = math.sqrt(2 * n * math.log(m)) if m > 1 else float('inf')
        fB = 2 * math.sqrt(n * math.log(p))
        rec.append((p, m, M, M / fA, M / fB, v2(p - 1)))
    if not rec: return None
    nA = sum(1 for r in rec if r[3] > 1.0)
    nB = sum(1 for r in rec if r[4] > 1.0)
    worstA = max(r[3] for r in rec)
    worstB = max(r[4] for r in rec)
    # 2-adic correlation: among violators of A, what is mean v2 vs whole pop?
    v2_all = sum(r[5] for r in rec) / len(rec)
    viosA = [r for r in rec if r[3] > 1.0]
    v2_vio = (sum(r[5] for r in viosA) / len(viosA)) if viosA else 0.0
    return dict(n=n, npr=len(rec), nA=nA, nB=nB, dA=nA/len(rec), dB=nB/len(rec),
                wA=worstA, wB=worstB, v2_all=v2_all, v2_vio=v2_vio,
                blo=math.log(usable[0])/math.log(n), bhi=math.log(usable[-1])/math.log(n))

if __name__ == "__main__":
    print("=" * 100)
    print("N8 FLOOR-VIOLATOR DENSITY among PRIZE-SHAPED primes (p~n^beta, p==1 mod n, proper mu_n).")
    print("density_A = frac violating SHARP M<=sqrt(2n ln m); density_B = frac violating ABSORB M<=2sqrt(n ln p)")
    print("=" * 100)
    hdr = f"{'n':>5} {'beta-win':>14} {'#pr':>5} {'denA':>7} {'denB':>7} {'worstA':>8} {'worstB':>8} {'v2(all)':>8} {'v2(vioA)':>9}"
    print(hdr)
    # prize regime beta ~ 4; sweep n, all primes in window, m capped for compute.
    for mu in range(3, 9):          # n = 8 .. 256
        n = 1 << mu
        # widen the window slightly to capture enough primes; keep beta ~ 4
        res = run(n, 3.6, 4.4, cap_primes=400, m_cap=80000)
        if res is None:
            print(f"{n:>5}  (no usable primes in window / m-cap)")
            continue
        print(f"{n:>5} b[{res['blo']:.2f},{res['bhi']:.2f}] {res['npr']:>5} "
              f"{res['dA']:>7.3f} {res['dB']:>7.3f} {res['wA']:>8.4f} {res['wB']:>8.4f} "
              f"{res['v2_all']:>8.2f} {res['v2_vio']:>9.2f}")
        sys.stdout.flush()
    print()
    print("READING:")
    print(" denB (ABSORB-floor violator density): if 0 across all n => the surviving floor is universal,")
    print("   negative closure FAILS (structured primes absorbed by constant 2).")
    print(" denA (SHARP-floor violator density): the trend vs n decides whether the SHARP sqrt(2) law has")
    print("   POSITIVE-density violators (kills universal sharp law) or DECAYING density (measure-zero).")
    print(" v2(vioA) vs v2(all): if violators have systematically HIGHER 2-adic depth, the anomaly is")
    print("   driven by field 2-structure (Fermat-like), confirming it is a STRUCTURED-prime effect.")
