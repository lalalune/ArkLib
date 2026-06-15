#!/usr/bin/env python3
# A1 (#444): EXACT n=64 (and re-confirm n=16,32) char-0 delta* sweep.
# Method: prime-size-independent (k+1)-subset solve via the DIVIDED-DIFFERENCE closed form for
# gamma (validated bit-exact vs full Gaussian solve), then per-(gamma-yielding)-subset interpolate
# the degree-<k poly and count TRUE agreement; per distinct gamma keep MAX agreement (all-subset
# max is required: one-subset-per-gamma undercounts higher bands -- verified). Worst over far
# pencils a,b in [k,n)\{n/2}, a<b. delta* = largest delta with worstI(delta) <= budget=n
# <=> w_cross = smallest band w with worstI(w) <= n ; delta* = 1 - w_cross/n.
# Parallelized across pencils with multiprocessing.
import itertools, math, time, sys, os, argparse
import numpy as np
from multiprocessing import Pool

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
        if p > want_min and isprime(p): return p
        t += 1

def proot(p, n):
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1: return h
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
        nz = (col % p) != 0; has = nz.any(axis=1); piv = np.argmax(nz, axis=1)
        singular |= ~has; idx = np.where(has)[0]
        if idx.size:
            r_c = M[idx, c, :].copy(); r_p = M[idx, piv[idx], :].copy()
            M[idx, c, :] = r_p; M[idx, piv[idx], :] = r_c
        pivval = M[:, c, c] % p; good = has & (pivval != 0); gidx = np.where(good)[0]
        if gidx.size:
            inv = vec_inv_modp(pivval[gidx], p)
            M[gidx, c, :] = (M[gidx, c, :] * inv[:, None]) % p
            factors = M[gidx][:, :, c].copy(); factors[np.arange(gidx.size), c] = 0
            sub = factors[:, :, None] * M[gidx, c, :][:, None, :]
            M[gidx, :, :] = (M[gidx, :, :] - sub) % p
    return M[:, :, s] % p, singular

# globals set per worker
_G = {}

def init_worker(n, k, p):
    z = proot(p, n)
    pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    powr = np.array([[pow(int(pts[i]), j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    _G['n'], _G['k'], _G['p'], _G['z'] = n, k, p, z
    _G['pts'], _G['powr'] = pts, powr
    _G['powrT'] = powr.T.astype(np.int64)

def pencil_worker(ab):
    a, b = ab
    n, k, p = _G['n'], _G['k'], _G['p']
    z, pts, powr, powrT = _G['z'], _G['pts'], _G['powr'], _G['powrT']
    za = np.array([pow(z, (i*a) % n, p) for i in range(n)], dtype=np.int64)
    zb = np.array([pow(z, (i*b) % n, p) for i in range(n)], dtype=np.int64)
    s = k+1; eye = np.eye(s, dtype=bool)
    gamma_max = np.zeros(p, dtype=np.int16)
    chunk = 1500000
    it = itertools.combinations(range(n), s)
    while True:
        block = list(itertools.islice(it, chunk))
        if not block: break
        combos = np.array(block, dtype=np.int64); C = combos.shape[0]
        X = pts[combos]
        diff = (X[:, :, None] - X[:, None, :]) % p
        diffm = np.where(eye[None, :, :], 1, diff)
        L = np.ones((C, s), dtype=np.int64)
        for j in range(s): L = (L * diffm[:, :, j]) % p
        Linv = vec_inv_modp(L.reshape(-1), p).reshape(C, s)
        num = (zb[combos] * Linv).sum(axis=1) % p
        den = (za[combos] * Linv).sum(axis=1) % p
        good = den % p != 0
        if not good.any(): continue
        cg = combos[good]
        gamma = ((-num[good]) * vec_inv_modp(den[good], p)) % p
        fvals = (zb[None, :] + gamma[:, None] * za[None, :]) % p  # (Cg,n)
        kpts = cg[:, :k]
        Vk = powr[kpts]
        rows = np.arange(gamma.shape[0])[:, None]
        y = fvals[rows, kpts]
        cc, sing2 = batch_solve_modp(Vk, y, p)
        valid = ~sing2
        if valid.any():
            gv = (cc[valid] @ powrT) % p
            ag = (gv == fvals[valid]).sum(axis=1).astype(np.int16)
            np.maximum.at(gamma_max, gamma[valid], ag)
    seen = gamma_max[gamma_max > 0]
    Iw = {w: int((seen >= w).sum()) for w in range(k+1, n+1)}
    maxag = int(seen.max()) if seen.size else 0
    return (a, b, Iw, maxag)

def far_pencils(n, k):
    fars = [x for x in range(k, n) if x != n//2]
    return [(a, b) for a in fars for b in fars if a < b]

def run(n, k, procs=8, pencils=None, label=""):
    p = find_prime(n, (n**3)*4)
    rho = k/n; cap = 1-rho; john = 1-math.sqrt(rho)
    if pencils is None: pencils = far_pencils(n, k)
    print(f"\n=== {label} n={n} k={k} rho={rho:.4f} p={p} (p/n^3={p/n**3:.1f}) "
          f"C(n,k+1)={math.comb(n,k+1):,} #pencils={len(pencils)} procs={procs} ===", flush=True)
    worst = {w: 0 for w in range(k+1, n+1)}
    worst_pencil = {w: None for w in range(k+1, n+1)}
    global_maxag = 0; maxag_pencil = None
    t0 = time.time()
    with Pool(procs, initializer=init_worker, initargs=(n, k, p)) as pool:
        for cnt, (a, b, Iw, maxag) in enumerate(pool.imap_unordered(pencil_worker, pencils, chunksize=1)):
            for w, v in Iw.items():
                if v > worst[w]:
                    worst[w] = v; worst_pencil[w] = (a, b)
            if maxag > global_maxag:
                global_maxag = maxag; maxag_pencil = (a, b)
            if (cnt+1) % max(1, len(pencils)//20) == 0 or cnt+1 == len(pencils):
                cross = next((w for w in range(k+1, n+1) if worst[w] <= n), None)
                print(f"  [{cnt+1}/{len(pencils)}] elapsed={time.time()-t0:.0f}s "
                      f"running w_cross={cross} max_agree={global_maxag}({maxag_pencil})", flush=True)
    cross = next((w for w in range(k+1, n+1) if worst[w] <= n), None)
    band = [worst[w] for w in range(k+1, n+1)]
    print(f"  worstI per band (w={k+1}..{n}): {band}")
    print(f"  GLOBAL max agreement over far pencils = {global_maxag} at pencil {maxag_pencil}")
    if cross is not None:
        dstar = 1 - cross/n; gap = cap - dstar
        Crho = (cross-k)/math.log2(n)
        print(f"  *** w_cross={cross} (worst pencil {worst_pencil[cross]}) delta*={dstar:.5f}")
        print(f"  *** w_cross-k={cross-k}  log2(n)={math.log2(n):.3f}  C_rho_est={Crho:.4f}")
        print(f"  *** n*(cap-delta*)={n*gap:.4f}  cap={cap:.4f} Johnson={john:.4f}")
        return dict(n=n, k=k, rho=rho, p=p, w_cross=cross, wmk=cross-k, log2n=math.log2(n),
                    dstar=dstar, cap=cap, gap=gap, Crho=Crho, pencil=worst_pencil[cross],
                    maxag=global_maxag, band=band)
    else:
        print("  NO crossing (worstI never <= n)")
        return dict(n=n, k=k, rho=rho, p=p, w_cross=None, maxag=global_maxag, band=band)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", type=str, default="all", help="comma cases like 16:2,32:4,64:4 or 'all'")
    ap.add_argument("--procs", type=int, default=8)
    args = ap.parse_args()
    cases = {
        "16:2": (16, 2), "32:4": (32, 4), "16:4": (16, 4),
        "32:2": (32, 2), "64:4": (64, 4), "32:8": (32, 8), "16:1": (16, 1),
    }
    if args.only == "all":
        order = ["16:2", "32:4", "16:4", "32:2", "64:4"]
    else:
        order = args.only.split(",")
    results = []
    for key in order:
        n, k = cases[key]
        results.append(run(n, k, procs=args.procs, label=key))
    print("\n\n############ SUMMARY (#444 A1) ############")
    print(f"{'rho':>8} {'n':>4} {'k':>3} {'w_cross':>8} {'w-k':>5} {'log2n':>6} {'C_rho':>7} {'delta*':>9} {'n*gap':>7} {'maxag':>6}")
    for r in results:
        if r.get('w_cross') is None:
            print(f"{r['k']/r['n']:>8.4f} {r['n']:>4} {r['k']:>3}   NO-CROSS  maxag={r['maxag']}"); continue
        print(f"{r['rho']:>8.4f} {r['n']:>4} {r['k']:>3} {r['w_cross']:>8} {r['wmk']:>5} "
              f"{r['log2n']:>6.3f} {r['Crho']:>7.4f} {r['dstar']:>9.5f} {r['gap']*r['n']:>7.3f} {r['maxag']:>6}")
    print("\nCANDIDATE: n*(cap-delta*) = C_rho*log2(n)  i.e.  (w_cross-k) = C_rho*log2(n).")
