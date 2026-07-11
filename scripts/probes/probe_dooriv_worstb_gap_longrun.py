#!/usr/bin/env python3
"""
Door-(iv) Lane-1 probe (#464) — LONGEST MONOTONE RUN / near-AP stretch of the worst-b
gap sequence (a LOCAL extremal-combinatorics object, distinct from L2 spectral rank).

A sequence can be spectrally FULL-RANK (proven: [doorIV-worstb-gap-spectrum-fullrank]) yet
still contain an anomalously LONG monotone / near-arithmetic-progression run — a LOCAL
structure a structured small-ball bound could grip without multiplicative energy. This is
the last distinct gap-combinatorial object not yet measured.

THE QUESTION (frequency-SENSITIVE => passes rule-3 only if it DIFFERS at b* vs generic b):
  L*(b) = longest run of consecutive gaps that is monotone (non-decr or non-incr).
  If L*(b*) is anomalously LARGE (>> O(log n) or ~ c*n) and LARGER than generic b, that is
  an exploitable local lever. If L*(b*) is O(1)/O(log n) and ~ generic, DEAD.

Prize regime: PROPER mu_n, p == 1 mod n, p ~ n^4 >> n^3, never n=q-1. UNIFORM coset-rep
sampling. EXACT integer gaps. Multiple structured primes; median. Empirical only.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, beta, count):
    target = n**beta; lo = max(target//2, n**3 + 1); out = []
    k = (lo-1)//n + 1
    while len(out) < count and k < 50_000_000:
        p = 1 + k*n
        if p > lo and is_prime(p): out.append(p)
        k += 1
    return out

def subgroup_mu_n(p, n):
    m = p-1; fac = set(); mm = m; d = 2
    while d*d <= mm:
        while mm % d == 0: fac.add(d); mm //= d
        d += 1
    if mm > 1: fac.add(mm)
    g = None
    for cand in range(2, p):
        if all(pow(cand, m//q, p) != 1 for q in fac): g = cand; break
    h = pow(g, (p-1)//n, p); mu = []; x = 1
    for _ in range(n): mu.append(x); x = (x*h) % p
    return mu

def eta_abs2(b, mu, p):
    s = 0j
    for x in mu:
        ang = 2*math.pi*((b*x) % p)/p; s += cmath.exp(1j*ang)
    return s.real*s.real + s.imag*s.imag

def gap_sequence(b, mu, p):
    pos = sorted(((b*x) % p) for x in mu); N = len(pos)
    return [(pos[(i+1) % N] - pos[i]) % p for i in range(N)]

def longest_monotone_run(seq):
    """longest circular run of consecutive gaps that is monotone non-decreasing OR non-increasing."""
    N = len(seq); ext = seq + seq  # circular: scan length 2N-1 windows but cap run at N
    best = 1
    # non-decreasing
    for start in range(N):
        run = 1
        for i in range(start, start + N - 1):
            if ext[i+1] >= ext[i]: run += 1
            else: break
        best = max(best, min(run, N))
    # non-increasing
    for start in range(N):
        run = 1
        for i in range(start, start + N - 1):
            if ext[i+1] <= ext[i]: run += 1
            else: break
        best = max(best, min(run, N))
    return best

def main():
    print("# Door-IV worst-b gap LONGEST-MONOTONE-RUN probe (#464)")
    print("# columns: n  p  worstb  Lrun(b*)  | generic Lrun   (random ref ~ O(log n))")
    import statistics as st
    for n in [16, 32, 64]:
        ps = primes_1_mod_n(n, 4, 5)
        if not ps:
            print(f"# n={n}: no primes"); continue
        ls_star, ls_gen = [], []
        for p in ps:
            mu = subgroup_mu_n(p, n); random.seed(464 + p); m = (p-1)//n
            seen = {}; cands = []; tries = 0
            while len(cands) < min(300, m) and tries < 3000:
                b = random.randrange(1, p); cmin = min((b*x) % p for x in mu)
                if cmin not in seen: seen[cmin] = b; cands.append(b)
                tries += 1
            bstar = max(cands, key=lambda b: eta_abs2(b, mu, p))
            lstar = longest_monotone_run(gap_sequence(bstar, mu, p))
            genb = random.choice([b for b in cands if b != bstar]) if len(cands) > 1 else bstar
            lgen = longest_monotone_run(gap_sequence(genb, mu, p))
            ls_star.append(lstar); ls_gen.append(lgen)
            print(f"  n={n:3d}  p={p:>10d}  b*={bstar:>9d}  Lrun*={lstar:>3d}  | gen={lgen:>3d}")
        ms = st.median(ls_star); mg = st.median(ls_gen)
        logn = math.log2(n)
        anomalous = "ANOMALOUS-LONG (LIVE?)" if ms > 3*logn and ms > mg else "O(log n)-ish, ~generic => DEAD"
        print(f"# n={n}: median Lrun(b*)={ms}  generic={mg}  (2*log2 n = {2*logn:.1f}; n = {n})  verdict: {anomalous}")
    print("# DONE")

if __name__ == "__main__":
    main()
