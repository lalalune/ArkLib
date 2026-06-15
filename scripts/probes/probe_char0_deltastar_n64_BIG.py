#!/usr/bin/env python3
# A1 (#444): n=64 decisive test of char-0 delta* candidate, CHUNKED combos to fit memory.
# Self-contained (no cross-file import). Same (k+1)-subset-solve method as
# probe_char0_deltastar_n64.py, but processes the C(n,k+1) subsets in chunks to bound RAM.
import itertools, math, time, sys, os
import numpy as np

def isprime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def find_prime(n, want_min):
    t = (want_min // n) + 1
    while True:
        p = 1 + n*t
        if p > want_min and isprime(p):
            return p
        t += 1

def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return h
    raise RuntimeError("no proot")

def vec_inv_modp(a, p):
    # vectorized modular inverse a^{p-2} mod p via square-and-multiply on int64 arrays.
    # a values in [1,p-1]. Returns int64 array of inverses (0 where a==0, but caller masks those).
    a = a.astype(np.int64) % p
    result = np.ones_like(a)
    base = a.copy()
    e = p - 2
    while e > 0:
        if e & 1:
            result = (result * base) % p
        e >>= 1
        if e:
            base = (base * base) % p
    return result

def batch_solve_modp(A, B, p):
    A = A.astype(np.int64) % p
    B = (B.astype(np.int64)) % p
    m, s, _ = A.shape
    singular = np.zeros(m, dtype=bool)
    M = np.concatenate([A, B[:, :, None]], axis=2)  # (m, s, s+1)
    for c in range(s):
        col = M[:, :, c].copy()
        col[:, :c] = 0
        nz = (col % p) != 0
        has = nz.any(axis=1)
        piv = np.argmax(nz, axis=1)
        singular |= ~has
        idx = np.where(has)[0]
        if idx.size:
            r_c = M[idx, c, :].copy()
            r_p = M[idx, piv[idx], :].copy()
            M[idx, c, :] = r_p
            M[idx, piv[idx], :] = r_c
        pivval = M[:, c, c] % p
        good = has & (pivval != 0)
        gidx = np.where(good)[0]
        if gidx.size:
            inv = vec_inv_modp(pivval[gidx], p)
            M[gidx, c, :] = (M[gidx, c, :] * inv[:, None]) % p
            factors = M[gidx][:, :, c].copy()
            factors[np.arange(gidx.size), c] = 0
            sub = factors[:, :, None] * M[gidx, c, :][:, None, :]
            M[gidx, :, :] = (M[gidx, :, :] - sub) % p
    x = M[:, :, s] % p
    return x, singular

def pencil_I_chunked(p, n, k, a, b, powr, za, zb, chunk=400000, verbose=False):
    # gamma_max[g] = max true agreement over all (k+1)-subsets that yield gamma g (0 = unseen).
    s = k+1
    powrT = powr.T.astype(np.int64)
    gamma_max = np.zeros(p, dtype=np.int16)  # agreement <= n <= 256, fits int16
    it = itertools.combinations(range(n), s)
    total = math.comb(n, s)
    done = 0; t0 = time.time()
    while True:
        block = list(itertools.islice(it, chunk))
        if not block: break
        combos = np.array(block, dtype=np.int64)
        Vsub = powr[combos]
        zacol = (-za[combos]) % p
        A = np.concatenate([Vsub, zacol[:, :, None]], axis=2)
        B = zb[combos]
        x, singular = batch_solve_modp(A, B, p)
        valid = ~singular
        if valid.any():
            g = x[valid][:, :k]; gamma = x[valid][:, k]
            gvals = (g @ powrT) % p
            fvals = (zb[None, :] + gamma[:, None] * za[None, :]) % p
            agree = (gvals == fvals).sum(axis=1).astype(np.int16)
            np.maximum.at(gamma_max, gamma, agree)
        done += len(block)
        if verbose:
            print(f"      chunk done={done:,}/{total:,} elapsed={time.time()-t0:.1f}s", flush=True)
    # I(w) = #{gamma : gamma_max >= w} ; gamma=0 with max 0 means unseen -> excluded automatically
    seen = gamma_max[gamma_max > 0]
    Iw = {w: int((seen >= w).sum()) for w in range(k+1, n+1)}
    return Iw

def deltastar_big(n, k, p, pencils, chunk=400000, verbose=True):
    z = proot(p, n)
    pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    powr = np.array([[pow(int(pts[i]), j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    worst = {w: 0 for w in range(k+1, n+1)}
    worst_pencil = {w: None for w in range(k+1, n+1)}
    t0 = time.time()
    for idx, (a, b) in enumerate(pencils):
        za = np.array([pow(z, (i*a) % n, p) for i in range(n)], dtype=np.int64)
        zb = np.array([pow(z, (i*b) % n, p) for i in range(n)], dtype=np.int64)
        Iw = pencil_I_chunked(p, n, k, a, b, powr, za, zb, chunk, verbose=False)
        for w, v in Iw.items():
            if v > worst[w]:
                worst[w] = v; worst_pencil[w] = (a, b)
        cross = next((w for w in range(k+1, n+1) if worst[w] <= n), None)
        if verbose:
            print(f"  pencil {idx+1}/{len(pencils)} (a,b)=({a},{b}) -> "
                  f"I(w={k+1}..{k+8})={[Iw[w] for w in range(k+1, min(k+9,n+1))]} | "
                  f"running w_cross={cross} elapsed={time.time()-t0:.0f}s", flush=True)
    cross = next((w for w in range(k+1, n+1) if worst[w] <= n), None)
    return worst, cross, worst_pencil

def select_pencils_n64(n, k):
    fars = [x for x in range(k, n) if x != n//2]
    pairs = [(a, b) for a in fars for b in fars if a < b]
    rep = []
    for (a, b) in pairs:
        d = (b - a) % n
        g = math.gcd(d if d else n, n)
        if g == 1:
            if a <= k+8 or abs(a - n//2) <= 4 or abs(b - n//2) <= 4:
                rep.append((a, b))
    seen = {}
    for (a, b) in pairs:
        d = (b - a) % n
        g = math.gcd(d if d else n, n)
        if g > 1:
            seen.setdefault(g, 0)
            if seen[g] < 4:
                rep.append((a, b)); seen[g] += 1
    return sorted(set(rep))

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=64)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--chunk", type=int, default=400000)
    ap.add_argument("--maxpencils", type=int, default=0)
    ap.add_argument("--allfar", action="store_true")
    args = ap.parse_args()
    n, k = args.n, args.k
    p = find_prime(n, (n**3)*4)
    rho = k/n; cap = 1-rho; john = 1-math.sqrt(rho)
    if args.allfar:
        fars = [x for x in range(k, n) if x != n//2]
        pencils = [(a, b) for a in fars for b in fars if a < b]
    else:
        pencils = select_pencils_n64(n, k)
    if args.maxpencils:
        pencils = pencils[:args.maxpencils]
    print(f"=== n={n} k={k} rho={rho:.4f} p={p} (p/n^3={p/n**3:.1f}) C(n,k+1)={math.comb(n,k+1):,} "
          f"#pencils={len(pencils)} chunk={args.chunk} ===", flush=True)
    t0 = time.time()
    worst, cross, wp = deltastar_big(n, k, p, pencils, args.chunk, verbose=True)
    band = [worst[w] for w in range(k+1, n+1)]
    print(f"\nworstI per band (w={k+1}..{n}): {band}")
    if cross is not None:
        dstar = 1 - cross/n; gap = cap - dstar
        print(f"\nRESULT n={n} k={k} rho={rho:.4f}: w_cross={cross} (pencil {wp[cross]}) delta*={dstar:.5f}")
        print(f"  w_cross-k = {cross-k}  log2(n)={math.log2(n):.3f}  C_rho_est={(cross-k)/math.log2(n):.4f}")
        print(f"  n*(cap-delta*)={n*gap:.4f}  cap={cap:.4f} Johnson={john:.4f}")
        print(f"  CANDIDATE: n*(cap-d*)=C_rho*log2(n) => {cross-k} == C_rho*{math.log2(n):.0f}")
    else:
        print("\nNO crossing (worstI never <= n)")
    print(f"total elapsed {time.time()-t0:.0f}s", flush=True)
