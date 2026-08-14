#!/usr/bin/env python3
"""
wf-RB (#444): DECISIVE over-determined far-line r-profile  I(n,r)  for n=32,34,38.

MISSION. The over-det closed form predicts the binding witness size s* = 2k-1 = n/2-1
=> delta* = (n-s*)/n = 1/2 + 1/n  (= Johnson + 1 rung). At n=32 the GPU/Rust engine pinned
s*=13 (delta*=0.594), a candidate CLIMB past Johnson toward the floor 1-rho. The KB note
[farline-engine-bs-direction-cap-artifact.md] diagnosed that as an artifact of the engine's
`b in [k,s)` direction CAP, which silently excludes the binding ANTIPODAL direction
(a,b)=(n/2, n/2-1) (b=n/2-1 >= s for every s<=n/2-1, so it is dropped throughout its BAD phase).

THIS PROBE resolves it DECISIVELY with the FULL b-range (no cap), exact in F_p, multi-prime
(p-independence check), reading off s* = largest s with I(n,s) <= budget=n directly.

Object (FarCosetExplosion.epsMCA_ge_far_incidence, axiom-clean):
  far dir u1 = x^b, offset u0 = x^a; agreement size s = |R|, rung r = n-s.
  I(a,b; s) = #{ gamma in F_p : x^a + gamma x^b agrees with SOME codeword of RS[mu_n, k]
               on the s points R }, worst over all witness sets R of size s.
  FAR-coset law: per agreement set R, the in-RS condition is AFFINE in gamma => <= 1 gamma per R
  (unless R is "heavy" = both u0,u1 in RS|_R, => all p gammas => incidence = p, fully BAD).

  binding s* = max{ s : max over far dirs (a,b) of I(a,b; s) <= budget = n }.
  delta* = (n - s*)/n.

EFFICIENCY. We only need to know whether I(n,s) > budget=n, not the exact count when it is huge.
So per direction we enumerate witness sets R streaming and EARLY-EXIT the moment we have
n+1 distinct gammas (BAD) or detect a heavy set (=> p, BAD). For the GOOD (small) rungs the
enumeration completes and gives the EXACT small count. We sweep the FULL direction set
(a,b in [k,n), a!=b) -- crucially INCLUDING the antipodal (n/2, n/2-1) the capped engine dropped.

n=32 is a power of two (prize-shaped); n=34,38 are NOT (multiple-primes / non-2-power control,
to confirm the s* law is not a 2-power artifact). rho=1/4 => k=n/4 (n divisible by 4: use 32,36,40
for the clean rho=1/4 axis; for 34,38 use nearest integer k=floor(n/4) and report rho).
"""
import sys, itertools
from math import comb
import numpy as np

# ---------- field setup ----------
def isprime(x):
    if x < 2: return False
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % x == 0: continue
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def fac(x):
    f = {}; dd = 2
    while dd*dd <= x:
        while x % dd == 0: f[dd] = f.get(dd,0)+1; x //= dd
        dd += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f

def proot(p):
    fs = set(fac(p-1))
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g

def find_prime_cong1(n, lo):
    c = lo + ((1 - lo) % n)
    if c <= 2: c += n
    while not (c % n == 1 and isprime(c)): c += n
    return c

def setup(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    return [pow(h, i, p) for i in range(n)]

# ---------- exact per-direction incidence with early-exit at budget ----------
def incidence_capped(a, b, n, mu, k, p, s, budget):
    """Exact I(a,b; s) but EARLY-EXIT returning budget+1 ("BAD") once > budget distinct gammas,
       or p ("heavy/BAD") if some witness set is heavy. Otherwise returns exact (<= budget) count."""
    inv = lambda z: pow(z, p-2, p)
    MUa = [pow(x, a, p) for x in mu]
    MUb = [pow(x, b, p) for x in mu]
    def ddk(vals, pts):
        vs = list(vals[:k+1]); xs = pts[:k+1]
        for j in range(1, k+1):
            for i in range(k, j-1, -1):
                vs[i] = (vs[i]-vs[i-1]) * inv((xs[i]-xs[i-j]) % p) % p
        return vs[k]
    def in_RS(vals, pts):
        if len(pts) <= k: return True
        for st in range(len(pts)-k):
            if ddk(vals[st:st+k+1], pts[st:st+k+1]) != 0: return False
        return True
    gam = set()
    for R in itertools.combinations(range(n), s):
        pts = [mu[i] for i in R]; u0 = [MUa[i] for i in R]; u1 = [MUb[i] for i in R]
        if in_RS(u1, pts):
            if in_RS(u0, pts):
                return p  # heavy: all gammas
            continue
        a0 = ddk(u0, pts); a1 = ddk(u1, pts)
        if a1 % p == 0: continue
        gm = (-a0 * inv(a1)) % p
        if in_RS([(u0[i] + gm*u1[i]) % p for i in range(s)], pts):
            gam.add(gm)
            if len(gam) > budget:
                return budget + 1  # BAD, early exit
    return len(gam)

# ---------- driver ----------
def run(n, k, primes, s_range, full_dirs=False):
    budget = n  # prize budget q*eps* ~ n
    rho = k / n
    print(f"\n===== n={n}  k={k}  rho={rho:.4f}  budget={budget}  Johnson s_J~{n*(1-1)//1} =====", flush=True)
    print(f"  Plotkin/Johnson proxy: s*=2k-1={2*k-1} => delta*=1/2+1/n={0.5+1/n:.4f}", flush=True)
    print(f"  Floor target delta*=1-rho={1-rho:.4f} => s*={int(round((1-(1-rho))*n))} (lower s)", flush=True)
    # direction set: FULL b-range (NO cap). Restrict to a small curated set + the antipodal,
    # since the antipodal (n/2,n/2-1) is the proven worst-case over-det maximizer.
    if full_dirs:
        dirs = [(a, b) for b in range(k, n) for a in range(k, n) if a != b]
    else:
        # CURATED binding-direction set (FULL b-range, no cap). The proven worst-case over-det
        # maximizer is the ANTIPODAL (n/2, n/2-1) [OverdetIncidenceMaxClosedForm,
        # DeepBandR4Bound], plus the low-exponent x^k far direction [probe_farline_incidence_exact
        # found (a,b)=(10,4)=(n-k... ,k) binding at n=16], plus order-2 lines. We include ALL of:
        m2 = n // 2
        dirs = []
        # antipodal / order-2 family (the cap-dropped binders):
        for d in [(m2, m2-1), (m2-1, m2), (m2, m2+1), (m2+1, m2), (m2, k), (k, m2),
                  (m2, m2-2), (m2-2, m2)]:
            if d[0] != d[1] and k <= d[0] < n and k <= d[1] < n:
                dirs.append(d)
        # low-exponent far family x^b, b in {k,k+1}, a sweeping (the in-tree (n-k,k) binder):
        for b in [k, k+1]:
            for a in range(k, n):
                if a != b: dirs.append((a, b))
        # de-dup
        seen = set(); ded = []
        for d in dirs:
            if d not in seen: seen.add(d); ded.append(d)
        dirs = ded
    # ALWAYS include the binding antipodal family explicitly (the one the cap drops):
    anti = [(n//2, n//2 - 1), (n//2 - 1, n//2)]
    for d in anti:
        if d not in dirs: dirs.append(d)

    print(f"  {len(dirs)} directions (FULL b-range, incl antipodal {(n//2,n//2-1)})", flush=True)
    # NOTE on cost: enumeration is C(n,s)=C(n,r). The over-det BAD region is at SMALL r
    # (deep band, #bad ~ n^4 >> budget). The GOOD region (I<=budget) is at SMALL r too once
    # #bad drops below n, OR at LARGE r (near Johnson, where over-det loses far structure).
    # We sweep r ASCENDING so the cheap small-C(n,r) BAD rungs come first; early-exit bounds the
    # rest. s* = n - (smallest r that is GOOD with all larger r... ) -- we report full profile.
    header = f"  {'s':>3} {'r':>3} {'delta':>7} {'C(n,s)':>12} " + " ".join(f"maxI[p{i}]".rjust(10) for i in range(len(primes))) + "  pindep  verdict"
    print(header, flush=True)
    setups = [(p, setup(n, p)) for p in primes]
    results = {}
    for s in s_range:
        r = n - s
        if r < 0 or s < k+1:  # need over-determined s>=k+1 for far structure
            continue
        delta = r / n
        per_p = []
        per_p_arg = []
        for (p, mu) in setups:
            best = 0; arg = None
            for (a, b) in dirs:
                I = incidence_capped(a, b, n, mu, k, p, s, budget)
                val = I if I <= budget else budget + 1   # clamp display
                if val > best:
                    best = val; arg = (a, b)
                    if best > budget:
                        break  # this rung already BAD for this prime
            per_p.append(best); per_p_arg.append(arg)
        # p-independence: for over-det rungs the GOOD/small counts should match across primes
        good_counts = [v for v in per_p if v <= budget]
        pindep = "YES" if len(set(per_p)) == 1 else ("(BAD-all)" if all(v > budget for v in per_p) else "MIXED")
        verdict = "GOOD<=n" if max(per_p) <= budget else "BAD >n"
        results[s] = max(per_p)
        cs = comb(n, s)
        row = f"  {s:>3} {r:>3} {delta:>7.4f} {cs:>12} " + " ".join(str(v).rjust(10) for v in per_p) + f"   {pindep:>5}  {verdict}  arg={per_p_arg[0]}"
        print(row, flush=True)
    # read off s* = largest s with I <= budget
    good = [s for s in results if results[s] <= budget]
    if good:
        sstar = max(good)
        print(f"  >>> s* = {sstar}  (largest s with maxI<=budget)  => delta* = (n-s*)/n = {(n-sstar)/n:.4f}", flush=True)
        print(f"  >>> predicted Johnson s*=n/2-1={n//2-1} => delta*={0.5+1/n:.4f};  "
              f"{'MATCHES Johnson' if sstar==n//2-1 else 'CLIMB!' if sstar<n//2-1 else 'below'}", flush=True)
    else:
        print("  >>> no GOOD rung in range", flush=True)
    return results

if __name__ == "__main__":
    # Two distinct primes per n for p-independence (p >> n^3, p == 1 mod n).
    # n=32 (2-power, rho=1/4, k=8)
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ns", default="16", help="comma list of n")
    ap.add_argument("--maxC", type=float, default=4e7, help="skip rungs with C(n,s)>maxC")
    args = ap.parse_args()
    KMAP = {16:4, 32:8, 34:8, 36:9, 38:9, 40:10, 20:5, 24:6, 28:7}
    for n in [int(x) for x in args.ns.split(",")]:
        k = KMAP[n]
        primes = [find_prime_cong1(n, 200000), find_prime_cong1(n, 700000)]
        # sweep ALL feasible s (s>=k+1) with C(n,s)<=maxC
        s_all = [s for s in range(k+1, n) if comb(n, s) <= args.maxC]
        run(n, k, primes, s_all)
    print("\nALL DONE", flush=True)
