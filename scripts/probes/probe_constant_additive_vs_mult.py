#!/usr/bin/env python3
"""Probe (#407): EXACT-CONSTANT test -- additive-G (Gaussian-sharp) vs multiplicative-1/c.

Decides whether the prize law  B = max_{coset}|eta_b| ~ sqrt(n * log(p/n))  has a
SHARP Gaussian constant (=> conjectured delta* constant H(rho)/beta is asymptotically
EXACT) or an INFLATED constant 1/sqrt(c) (=> delta* constant is wrong by 1/sqrt(c)).

Let  R(p) := max|eta_b|^2 / n  - ln(m),   m = (p-1)/n  [the residual over bare Gaussian].
 * ADDITIVE model  (KB salem-zygmund claim):  max|eta|^2/n = ln m + G,  G bounded
   => R(p) FLAT in ln m  => B/sqrt(n ln m) -> 1  (sharp).
 * MULTIPLICATIVE model (tail-constant c<1):   max|eta|^2/n = ln(m)/c
   => R(p) = (1/c - 1) ln m  GROWS LINEARLY in ln m  => B/sqrt(n ln m) -> 1/sqrt(c).

Method: fix small n; sweep p over a WIDE beta-range (ln m from ~5 to ~15); several
valid primes per ln-m bucket (exclude Fermat/fully-dyadic: require odd_part(m)>1);
average max|eta|^2/n per bucket; LINEAR-fit  max|eta|^2/n  vs  ln m.
   slope ~ 1, intercept = G bounded  => ADDITIVE / sharp (constant exact).
   slope = 1/c > 1                    => MULTIPLICATIVE / inflated (constant = 1/sqrt(c)).
"""
import sys, math
import numpy as np


def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True


def odd_part(x):
    while x % 2 == 0: x //= 2
    return x


def primitive_root(p):
    phi = p-1; facs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs): return g
    raise RuntimeError


def primes_near(n, target_m, want, used):
    """`want` valid primes with (p-1)/n ~ target_m, proper non-dyadic subgroup."""
    base = n*target_m + 1
    out = []; p = base - (base % n) + 1
    tries = 0
    while len(out) < want and tries < 200000:
        if p > 3 and is_prime(p) and odd_part((p-1)//n) > 1 and p not in used:
            out.append(p); used.add(p)
        p += n; tries += 1
    return out


def max_period_sq_over_n(p, n):
    """max over cosets of |eta_b|^2 / n  (b = g^j transversal). chunked numpy."""
    g = primitive_root(p); eta = pow(g, (p-1)//n, p)
    xs = np.array([pow(eta, i, p) for i in range(n)], dtype=np.int64)
    ncos = (p-1)//n; twp = 2.0*math.pi/p
    CH = max(1, min(4_000_000 // n, ncos))
    Gv = [1]*CH
    for i in range(1, CH): Gv[i] = Gv[i-1]*g % p
    best = -1.0; c = 1; j = 0
    while j < ncos:
        mlen = min(CH, ncos - j)
        reps = np.fromiter(((c*Gv[i]) % p for i in range(mlen)), dtype=np.int64, count=mlen)
        ang = ((reps[:,None]*xs[None,:]) % p).astype(np.float64)*twp
        S2 = np.cos(ang).sum(1)**2 + np.sin(ang).sum(1)**2
        mx = float(S2.max())
        if mx > best: best = mx
        c = c * pow(g, mlen, p) % p; j += mlen
    return best / n


def run(n, m_targets, per_bucket):
    print(f"\n{'='*84}\n n = {n}   (exact-constant additive-vs-mult test)\n{'='*84}")
    print(f" {'~m':>10} {'ln m':>7} {'#pr':>4} {'mean max|eta|^2/n':>18} {'-ln m (resid G)':>16} {'ratio':>7}")
    used = set(); X=[]; Y=[]
    for tm in m_targets:
        ps = primes_near(n, tm, per_bucket, used)
        vals = [max_period_sq_over_n(p, n) for p in ps]
        if not vals: continue
        mavg = sum(vals)/len(vals)
        lnm = math.log(((ps[0]-1)//n))
        # use per-prime exact ln m averaged
        lnms = [math.log((p-1)//n) for p in ps]
        lnm = sum(lnms)/len(lnms)
        X.append(lnm); Y.append(mavg)
        print(f" {tm:>10} {lnm:>7.3f} {len(ps):>4} {mavg:>18.3f} {mavg-lnm:>16.3f} {mavg/lnm:>7.3f}")
    X=np.array(X); Y=np.array(Y)
    A=np.vstack([X,np.ones_like(X)]).T
    (slope,intc),res,*_=np.linalg.lstsq(A,Y,rcond=None)
    ss_tot=((Y-Y.mean())**2).sum(); ss_res=float(res[0]) if len(res) else ((Y-A@[slope,intc])**2).sum()
    r2=1-ss_res/ss_tot
    print(f"\n  FIT  max|eta|^2/n = {slope:.3f}*ln(m) + {intc:.3f}   R^2={r2:.4f}")
    print(f"   ADDITIVE/sharp  => slope~1, intercept=G bounded  => B/sqrt(n ln m)->1")
    print(f"   MULTIPLICATIVE  => slope=1/c>1                   => B/sqrt(n ln m)->{math.sqrt(slope):.3f}")
    verdict = "ADDITIVE (sharp Gaussian constant; conj delta* constant asymptotically EXACT)" \
        if abs(slope-1) < 0.18 else \
        f"MULTIPLICATIVE slope={slope:.2f} (constant INFLATED by 1/sqrt(c)={math.sqrt(slope):.2f}; conj constant WRONG)"
    print(f"   >>> VERDICT (n={n}): {verdict}")
    return slope, intc, r2


def main():
    print("#"*84)
    print("# EXACT-CONSTANT PROBE: does B/sqrt(n log(p/n)) -> 1 (sharp) or -> 1/sqrt(c) (inflated)?")
    print("#"*84)
    # wide ln-m sweep; small n so many primes are cheap
    run(16, [60, 200, 700, 2500, 9000, 32000, 120000, 450000, 1600000], per_bucket=6)
    run(32, [60, 200, 700, 2500, 9000, 32000, 120000, 450000], per_bucket=5)
    print("\n"+"#"*84)
    print("# If BOTH n give slope ~1 with bounded intercept: KB's sharp-constant claim CONFIRMED,")
    print("#   conjectured delta* = 1-rho-H(rho)/(beta log n) has the EXACT constant (asymptotically).")
    print("# If slope > ~1.2 persistently: the constant is INFLATED -> delta* refinement needed.")
    print("#"*84)
    return 0


if __name__ == "__main__":
    sys.exit(main())
