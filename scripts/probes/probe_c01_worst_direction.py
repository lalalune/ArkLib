#!/usr/bin/env python3
"""
probe_c01_worst_direction.py  (#444 / C01 attack, FLUSHED, fast)

C01's load-bearing claim:  the incidence-MAXIMIZING far direction has gcd(b-a,n)=1
(so d=n/gcd=n), giving crossing offset s*-k = log2(n)  =>  delta*=(1-rho)-log2(n)/n.

We test this directly by computing, per far pencil, the exact char-0 worst-case
list size at each threshold t, and reporting AT THE CROSSING which gcd-class wins.
If a gcd>1 pencil (d=n/4) wins / matches with a LARGER offset than log2(n), C01-A
is refuted (the maximizer is not gcd=1, and the offset is not log2(n)).

Engine: same numpy-batched (k+1)-subset divided-difference solve as the in-tree
probe_char0_deltastar_n64_BIG.py.  PROPER subgroup mu_n < F_p*, p prime, p>>n^3,
never n=p-1.  p-independence (char-0 faithfulness) checked with two primes.
"""
import itertools, math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def find_primes(n, want_min, count=2):
    out = []
    t = (want_min // n) + 1
    while len(out) < count:
        p = 1 + n*t
        if p > want_min and isprime(p) and (p-1) != n:
            out.append(p)
        t += 1
    return out

def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return h
    raise RuntimeError("no proot")

def vec_inv_modp(a, p):
    a = a.astype(np.int64) % p
    result = np.ones_like(a); base = a.copy(); e = p - 2
    while e > 0:
        if e & 1: result = (result * base) % p
        e >>= 1
        if e: base = (base * base) % p
    return result

def batch_solve_modp(A, B, p):
    A = A.astype(np.int64) % p; B = (B.astype(np.int64)) % p
    m, s, _ = A.shape
    singular = np.zeros(m, dtype=bool)
    M = np.concatenate([A, B[:, :, None]], axis=2)
    for c in range(s):
        col = M[:, :, c].copy(); col[:, :c] = 0
        nz = (col % p) != 0
        has = nz.any(axis=1); piv = np.argmax(nz, axis=1)
        singular |= ~has
        idx = np.where(has)[0]
        if idx.size:
            r_c = M[idx, c, :].copy(); r_p = M[idx, piv[idx], :].copy()
            M[idx, c, :] = r_p; M[idx, piv[idx], :] = r_c
        pivval = M[:, c, c] % p
        good = has & (pivval != 0); gidx = np.where(good)[0]
        if gidx.size:
            inv = vec_inv_modp(pivval[gidx], p)
            M[gidx, c, :] = (M[gidx, c, :] * inv[:, None]) % p
            factors = M[gidx][:, :, c].copy(); factors[np.arange(gidx.size), c] = 0
            sub = factors[:, :, None] * M[gidx, c, :][:, None, :]
            M[gidx, :, :] = (M[gidx, :, :] - sub) % p
    return M[:, :, s] % p, singular

def pencil_Iw(p, n, k, a, b, combos, powr, za, zb):
    s = k+1
    Vsub = powr[combos]; zacol = (-za[combos]) % p
    A = np.concatenate([Vsub, zacol[:, :, None]], axis=2)
    B = zb[combos]
    x, singular = batch_solve_modp(A, B, p)
    valid = ~singular
    if not valid.any():
        return {w: 0 for w in range(k+1, n+1)}
    g = x[valid][:, :k]; gamma = x[valid][:, k]
    gvals = (g @ powr.T) % p
    fvals = (zb[None, :] + gamma[:, None] * za[None, :]) % p
    agree = (gvals == fvals).sum(axis=1)
    best = {}
    for gm, ag in zip(gamma.tolist(), agree.tolist()):
        if gm not in best or ag > best[gm]: best[gm] = ag
    vals = list(best.values())
    return {w: sum(1 for v in vals if v >= w) for w in range(k+1, n+1)}

def run(n, k):
    rho = k/n; cap = 1-rho; john = 1-math.sqrt(rho); budget = n
    primes = find_primes(n, (n**3)*4, 2)
    print(f"\n===== n={n} k={k} rho={rho:.4f} primes={primes} budget(n)={n} =====", flush=True)
    print(f"  Johnson 1-sqrt(rho)={john:.5f}, capacity 1-rho={cap:.5f}", flush=True)
    fars = [x for x in range(k, n) if x != n//2]
    pencils = [(a, b) for a in fars for b in fars if a < b]
    combos = np.array(list(itertools.combinations(range(n), k+1)), dtype=np.int64)
    results_per_p = {}
    for p in primes:
        z = proot(p, n)
        pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
        powr = np.array([[pow(int(pts[i]), j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
        worst = {w: 0 for w in range(k+1, n+1)}
        worst_pen = {w: None for w in range(k+1, n+1)}
        # also track, per gcd-class, the best offset achieved
        for (a, b) in pencils:
            za = np.array([pow(z, (i*a) % n, p) for i in range(n)], dtype=np.int64)
            zb = np.array([pow(z, (i*b) % n, p) for i in range(n)], dtype=np.int64)
            Iw = pencil_Iw(p, n, k, a, b, combos, powr, za, zb)
            for w, v in Iw.items():
                if v > worst[w]:
                    worst[w] = v; worst_pen[w] = (a, b)
        cross = next((w for w in range(k+1, n+1) if worst[w] <= budget), None)
        results_per_p[p] = (worst, cross, worst_pen)
        if cross is not None:
            a, b = worst_pen[cross] if worst_pen[cross] else (worst_pen[max(k+1, cross-1)])
            # the BAD pencil is the one at cross-1 (the largest-list pencil just inside)
            badw = cross - 1 if cross-1 >= k+1 else cross
            bp = worst_pen[badw]
            gb = math.gcd(((bp[1]-bp[0]) % n) or n, n) if bp else None
            d = n // gb if gb else None
            offset = cross - k
            print(f"  p={p}: s*=w_cross={cross}, offset s*-k={offset}, delta*={1-cross/n:.5f}", flush=True)
            print(f"        binding(bad) pencil just inside = {bp}, gcd(b-a,n)={gb}, d=n/gcd={d}", flush=True)
            print(f"        C01 says offset=log2(d)={math.log2(d):.2f} & worst gcd=1; campaign says offset=n/4={n/4}", flush=True)
            print(f"        worstI band w={k+1}..{min(n,k+10)}: {[worst[w] for w in range(k+1,min(n+1,k+11))]}", flush=True)
        else:
            print(f"  p={p}: NO crossing", flush=True)
    # p-independence
    if len(primes) == 2:
        w0 = results_per_p[primes[0]][0]; w1 = results_per_p[primes[1]][0]
        agree = all(w0[w] == w1[w] for w in w0)
        print(f"  p-INDEPENDENT (char-0 faithful): {'YES' if agree else 'NO'}", flush=True)
    # DIRECT C01-A test: at the crossing threshold, list the worst pencil PER gcd-class
    p = primes[0]; z = proot(p, n)
    pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    powr = np.array([[pow(int(pts[i]), j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    cross = results_per_p[p][1]
    if cross is None: return
    # report which gcd-class achieves the largest offset (largest threshold with list>budget)
    bestoff_by_gcd = {}
    for (a, b) in pencils:
        za = np.array([pow(z, (i*a) % n, p) for i in range(n)], dtype=np.int64)
        zb = np.array([pow(z, (i*b) % n, p) for i in range(n)], dtype=np.int64)
        Iw = pencil_Iw(p, n, k, a, b, combos, powr, za, zb)
        # the pencil's own crossing: smallest w with Iw<=budget; its offset = that w - k
        pc = next((w for w in range(k+1, n+1) if Iw[w] <= budget), None)
        if pc is None: continue
        off = pc - k
        g = math.gcd(((b-a) % n) or n, n)
        if g not in bestoff_by_gcd or off > bestoff_by_gcd[g][0]:
            bestoff_by_gcd[g] = (off, (a, b))
    print(f"  --- C01-A DIRECT TEST: max far-pencil crossing-offset PER gcd-class (p={p}) ---", flush=True)
    for g in sorted(bestoff_by_gcd):
        off, pen = bestoff_by_gcd[g]
        d = n // g
        print(f"     gcd={g:2d} (d=n/gcd={d:2d}, log2(d)={math.log2(d):.2f}): max offset={off}  pencil={pen}", flush=True)
    gmax = max(bestoff_by_gcd, key=lambda g: bestoff_by_gcd[g][0])
    print(f"  ==> WORST direction has gcd={gmax} (C01 requires gcd=1). "
          f"{'C01-A HOLDS' if gmax==1 else 'C01-A REFUTED (maximizer is NOT gcd=1)'}", flush=True)

if __name__ == "__main__":
    run(16, 2)   # rho=1/8 (the row log2(n) was fit on)
    run(32, 2)   # rho=1/16
    run(16, 4)   # rho=1/4 control
