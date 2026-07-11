#!/usr/bin/env python3
"""
probe_444_worstcoset_quotient_structure_b.py  (#444, door-(iv) adversarial re-check)

Adversarial re-check of probe_444_worstcoset_quotient_structure.py:
  (1) generator-INDEPENDENCE: re-run flatness with a SECOND generator g2. The set Wq and the
      Fourier-flatness of f(j)=|eta(g^j)| must not be an artifact of the generator choice
      (a different g is a multiplicative relabel j -> a*j of Z_m; flatness is dilation-invariant
      so ||hatf||_inf/||hatf||_2 must be IDENTICAL).
  (2) STRUCTURED Fermat-type primes (high 2-adic valuation v2(p-1)) where the prize is hardest:
      does the worst-coset profile gain ANY Fourier concentration? (If structured primes made
      Wq additively structured, that would be the door-(iv) crack.)
NO moment, NO completion, NO Lean.
"""
import cmath, math
import numpy as np

def isprime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if x % q == 0: return x == q
    d = x-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= x: continue
        y = pow(a, d, x)
        if y == 1 or y == x-1: continue
        ok = False
        for _ in range(r-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c

def prim_roots(p, want=2):
    x = p-1; fs = set(); d = 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    out = []
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fs):
            out.append(g)
            if len(out) >= want: break
    return out

def find_high_v2(n, beta, min_v2):
    """find p == 1 mod n, p ~ n^beta, with v2(p-1) >= min_v2 (structured)."""
    target = int(n**beta)
    mod = 1 << max(min_v2, v2(n))
    if n % mod != 0:
        mod = n if v2(n) >= min_v2 else (1 << min_v2)
    # require both n | p-1 and 2^min_v2 | p-1
    step = n
    while v2(step) < min_v2: step *= 2  # ensure step carries the 2-adic depth
    start = (target // step) * step + 1
    for k in range(0, 4000000):
        for cand in (start + k*step, start - k*step):
            if cand > n and isprime(cand) and (cand-1) % n == 0 and v2(cand-1) >= min_v2:
                return cand
    return None

def profile(n, p, g):
    m = (p-1)//n
    w = cmath.exp(2j*math.pi/p)
    gm = pow(g, m, p)
    mu = [pow(gm, t, p) for t in range(n)]
    mag = np.empty(m)
    gj = 1
    for j in range(m):
        s = 0j
        for x in mu:
            s += w**((gj*x) % p)
        mag[j] = abs(s)
        gj = (gj*g) % p
    return mag, m

def flat_stat(mag):
    f = mag - mag.mean()
    F = np.abs(np.fft.fft(f))[1:]
    l2 = math.sqrt((F**2).sum())
    return (F.max()/l2 if l2 > 0 else 0.0)

if __name__ == "__main__":
    print("=== (1) generator-independence of flatness ===")
    for (n, beta) in [(8,4.0),(8,4.5),(16,4.0)]:
        p = None
        target = int(n**beta); start = (target//n)*n + 1
        for k in range(0, 2000000):
            for cand in (start+k*n, start-k*n):
                if cand > n and isprime(cand) and ((cand-1)//n) % 2 == 1:
                    p = cand; break
            if p: break
        gs = prim_roots(p, want=2)
        if len(gs) < 2: 
            print(f"  n={n} p={p}: <2 generators"); continue
        m = (p-1)//n
        if m*n > 4_000_000:
            print(f"  n={n} p={p} m={m}: too big"); continue
        s1 = flat_stat(profile(n, p, gs[0])[0])
        s2 = flat_stat(profile(n, p, gs[1])[0])
        print(f"  n={n} p={p} m={m}: flat(g={gs[0]})={s1:.5f}  flat(g={gs[1]})={s2:.5f}  IDENTICAL={abs(s1-s2)<1e-9}")
    print("=== (2) structured high-v2 (Fermat-type) primes: any Fourier concentration in worst-coset profile? ===")
    for (n, beta, minv2) in [(8,4.0,8),(8,4.5,10),(16,4.0,9),(16,4.5,12),(32,4.0,10)]:
        p = find_high_v2(n, beta, minv2)
        if p is None:
            print(f"  n={n} beta={beta} v2>={minv2}: none found"); continue
        m = (p-1)//n
        if m*n > 8_000_000:
            print(f"  n={n} p={p} m={m} v2={v2(p-1)}: too big, skip"); continue
        g = prim_roots(p, 1)[0]
        mag, m = profile(n, p, g)
        M = mag.max()
        Wq10 = [j for j in range(m) if mag[j] >= 0.90*M]
        s = flat_stat(mag)
        base = 1/math.sqrt(m/2)
        print(f"  n={n} p={p} m={m} v2(p-1)={v2(p-1)} beta_eff={math.log(p,n):.2f}  M/sqrtn={M/math.sqrt(n):.3f}  |Wq@10%|={len(Wq10)}  flat={s:.5f} (base {base:.5f}, ratio {s/base:.2f})")
    print("=== done ===")
