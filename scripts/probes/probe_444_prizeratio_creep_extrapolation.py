#!/usr/bin/env python3
# DOOR-IV Lane-1, frontier-movement (NON-redundant): the OPEN question flagged in DISPROOF_LOG:10803 is
# whether the ACTUAL prize ratio  R(n) = M(n)/sqrt(2 n log p)  CREEPS UP without bound (prize in danger /
# at least not a fixed-C law from this data) or SATURATES (consistent with a fixed-C prize bound).
# Prior measured sequence (n=8,16,32,64): R = 0.655, 0.735, 0.772, 0.835.  Two more points (n=128,256)
# distinguish:  log-of-log bounded correction (saturating)  vs  power-law  vs  +c/sqrt(log) approach->1.
#
# M(n) = max_{b != 0} | sum_{x in mu_n} e_p(b x) |, mu_n the THIN 2-power subgroup (n=2^a), p == 1 mod n,
# v2(p-1) = log2 n ("good"/prize-rep prime), beta = log_n p ~ 4 (prize regime). PROPER subgroup, p >> n^3,
# NEVER n = q-1. Exact S1 convention.
#
# Speed trick (the reason this beats the killed pure-python n256 loop): build the coset transversal
# t_k = (g^n)^k mod p for k=0..m-1 with VECTORIZED numpy (chunked cumulative modmul, no python list of 16M),
# then M = max over the transversal of |sum_x cos + i sin|. p < 2^32 so t*x < 2^64 fits uint64 exactly.
import math, numpy as np, time

def isp(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def proot(p):
    m = p-1; fs = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fs.append(m)
    g = 2
    while not all(pow(g, (p-1)//f, p) != 1 for f in fs): g += 1
    return g

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def good_prime_near(n, target, cap):
    # smallest prime p >= target (capped < cap), p == 1 mod n, v2(p-1) = log2 n (m odd = "good").
    # target = n^beta with beta~4 (PRIZE regime). Keeps m=(p-1)/n at the intended ~n^3 scale.
    mu2 = int(round(math.log2(n)))
    p = target + ((1 + n - target % n) % n)   # first p == 1 mod n at or above target
    while p < cap:
        if p % n == 1 and isp(p) and v2(p-1) == mu2:
            return p
        p += n
    # fall back: largest good prime below cap (only triggers when n^4 ~ cap, i.e. n=256)
    p = cap - (cap % n) + 1
    if p >= cap: p -= n
    while p > n:
        if p % n == 1 and isp(p) and v2(p-1) == mu2:
            return p
        p -= n
    return None

def build_transversal_vec(gn, p, m):
    # t_k = gn^k mod p, k=0..m-1, vectorized: fill in chunks using a running scalar base per chunk.
    # numpy uint64 modmul: (a*b) % p exact while a,b < p < 2^32.
    out = np.empty(m, dtype=np.uint64)
    P = np.uint64(p)
    CH = 1 << 20  # 1M per chunk
    base = 1  # gn^(chunk_start)
    # precompute gn^j for j in 0..CH-1 once (the chunk template), then multiply by base each chunk
    tmpl = np.empty(min(CH, m), dtype=np.uint64)
    b = 1
    for j in range(len(tmpl)):
        tmpl[j] = b
        b = b * gn % p
    gn_CH = b  # = gn^CH  (b after the loop is gn^len(tmpl))
    # tmpl[j] = gn^j < p < 2^32, base < p < 2^32  =>  tmpl*base < 2^64 : EXACT in uint64, no object array.
    Pu = np.uint64(p)
    i = 0
    while i < m:
        L = min(CH, m - i)
        bu = np.uint64(base)
        out[i:i+L] = (tmpl[:L] * bu) % Pu     # pure uint64, exact (both factors < 2^32)
        base = base * gn_CH % p
        i += L
    return out

def M_of_n(n, p):
    g = proot(p)
    h = pow(g, (p-1)//n, p)          # generator of mu_n
    m = (p-1)//n
    gn = pow(g, n, p)                # generator of the transversal (coset reps of mu_n in F_p*)
    mu = [pow(h, j, p) for j in range(n)]
    bl = build_transversal_vec(gn, p, m)   # all b != 0 reps, vectorized
    c = 2.0*np.pi/p
    P = np.uint64(p)
    re = np.zeros(m, dtype=np.float64)
    im = np.zeros(m, dtype=np.float64)
    for x in mu:
        t = (bl * np.uint64(x)) % P          # uint64 exact, p < 2^32
        ang = c * t.astype(np.float64)
        re += np.cos(ang); im += np.sin(ang)
    mag = np.sqrt(re*re + im*im)
    idx = int(np.argmax(mag))
    return float(mag[idx]), m, int(bl[idx])

def main():
    print("# DOOR-IV Lane-1: prize-ratio creep extrapolation  R(n)=M(n)/sqrt(2 n log p),  beta~4, good prime")
    print("# extends DISPROOF_LOG:10803 sequence R(n=8,16,32,64)=0.655,0.735,0.772,0.835 to n=128,256")
    rows = []
    for n in (8, 16, 32, 64, 128, 256):
        cap = 1 << 32                       # exact uint64 modmul requires p < 2^32 (t*x < 2^64)
        target = int(round(n ** 4.0))       # PRIZE regime beta~4  => m=(p-1)/n ~ n^3 (8,16,32,64: tiny;
                                            # 128: m~2M; 256: n^4=2^32 at the cap, falls back to ~16M)
        p = good_prime_near(n, target, cap)
        if p is None:
            print(f"  n={n}: no good prime found"); continue
        beta = math.log(p)/math.log(n)
        t0 = time.time()
        M, m, bstar = M_of_n(n, p)
        dt = time.time()-t0
        denom = math.sqrt(2.0*n*math.log(p))
        R = M/denom
        rows.append((n, p, beta, M, R, dt))
        print(f"  n={n:3d} p={p:>11} beta={beta:.2f} m={m:>9} M={M:8.3f} R=M/sqrt(2n log p)={R:.4f}  ({dt:.1f}s)", flush=True)
    print()
    # extrapolation diagnostics: is R bounded? fit R vs log log p, R vs log p, R vs n^eps
    if len(rows) >= 4:
        import numpy as _np
        ns = _np.array([r[0] for r in rows], float)
        Rs = _np.array([r[4] for r in rows], float)
        ps = _np.array([r[1] for r in rows], float)
        # successive ratios of (1-R) — if 1-R -> 0 geometrically, R saturates to 1
        print("  successive R increments:", [f"{Rs[i+1]-Rs[i]:.4f}" for i in range(len(Rs)-1)])
        print("  R vs log2(n):           ", [f"n={int(ns[i])}:{Rs[i]:.3f}" for i in range(len(Rs))])
        # linear fit R ~ a + b*log(log p): if extrapolated R(n=2^30) stays < ~1.5, consistent w fixed C
        llp = _np.log(_np.log(ps))
        A = _np.vstack([_np.ones_like(llp), llp]).T
        coef, *_ = _np.linalg.lstsq(A, Rs, rcond=None)
        # predict at prize n=2^30, p~n^4
        n30 = 2.0**30; p30 = n30**4
        Rpred_llp = coef[0] + coef[1]*math.log(math.log(p30))
        # power-law fit R ~ a * n^b
        lns = _np.log(ns); B = _np.vstack([_np.ones_like(lns), lns]).T
        coefp, *_ = _np.linalg.lstsq(B, _np.log(Rs), rcond=None)
        Rpred_pow = math.exp(coefp[0] + coefp[1]*math.log(n30))
        print(f"  fit R ~ a+b*loglog p : a={coef[0]:.3f} b={coef[1]:.3f} -> R(n=2^30) ~ {Rpred_llp:.3f}")
        print(f"  fit R ~ a*n^b        : a={math.exp(coefp[0]):.3f} b={coefp[1]:.4f} -> R(n=2^30) ~ {Rpred_pow:.3f}")
        print()
        print("  READ: power-law exponent b>0 (R~n^b unbounded) => the prize FIXED-C law is NOT supported by")
        print("        this data (creep is a power, not a log correction). b~0 / loglog fit bounded => the")
        print("        creep is a sqrt-log/loglog correction, consistent with M<=C sqrt(n log(p/n)) (prize).")
        print("  CAVEAT (asymptotic-claim guard): n<=256 cannot DECIDE a 25-yr open asymptotic. This MEASURES")
        print("        which extrapolation the finite data favors; it is NOT a proof either way. CORE stays OPEN.")

if __name__ == '__main__':
    main()
