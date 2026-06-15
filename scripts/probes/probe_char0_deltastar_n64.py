#!/usr/bin/env python3
# A1 (#444): TEST THE CHAR-0 delta* CANDIDATE AT n=64 (decisive), re-confirm n=16,32,
# and pin C_rho's rho-dependence.
#
# Candidate (constant rate rho=k/n):  n*(cap - delta*) = C_rho * log2(n),  cap = 1-rho.
# Equivalently the crossing band w_cross satisfies  w_cross - k = C_rho * log2(n).
#
# Method (prime-size-independent (k+1)-subset solve, batched in numpy mod p):
#  RS[k] over mu_n (n-th roots of unity z^0..z^{n-1}, z a primitive n-th root mod prime p>>n^3).
#  A far "pencil" (a,b) with a,b in [k,n)\{n/2}, a<b: the codeword family is the function
#      f_gamma(alpha) = alpha^a + gamma*alpha^b   on the n eval points.
#  For each (k+1)-subset A of the n points: require f_gamma to agree with ONE degree-<k poly g
#  on all of A. That is k+1 equations [ Vander_{<k}(A) | -za(A) ] (g;gamma) = zb(A), i.e.
#  (k+1)x(k+1) linear system. Solve over F_p -> (g, gamma). Then count TRUE agreement of f_gamma
#  with g over all n points. For each distinct gamma keep its max agreement.
#  I(w) = #{ distinct gamma : maxagreement(gamma) >= w }.
#  Worst over far pencils: worstI(w) = max over (a,b) of I_{a,b}(w).
#  delta* = largest delta with worstI <= budget=n  <=>  w_cross = smallest w with worstI(w) <= n,
#  delta* = 1 - w_cross/n.
import itertools, math, sys, time
import numpy as np

def isprime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def find_prime(n, want_min):
    # smallest prime p > want_min with n | p-1
    # p = 1 + n*t
    t = (want_min // n) + 1
    while True:
        p = 1 + n*t
        if p > want_min and isprime(p):
            return p
        t += 1

def proot(p, n):
    # primitive n-th root of unity mod p: h^n=1, h^{n/2}!=1
    for c in range(2, p):
        h = pow(c, (p-1)//n, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return h
    raise RuntimeError("no proot")

def batch_solve_modp(A, B, p):
    # A: (m, s, s) int64 matrices ; B: (m, s) int64 rhs ; solve A x = B mod p (p prime) via
    # vectorized Gaussian elimination. Returns x:(m,s) and singular mask (bool, m).
    A = A.astype(object) if False else A.copy().astype(np.int64) % p
    B = (B.copy().astype(np.int64)) % p
    m, s, _ = A.shape
    singular = np.zeros(m, dtype=bool)
    # augmented
    M = np.concatenate([A, B[:, :, None]], axis=2)  # (m, s, s+1)
    for c in range(s):
        # find pivot: first row >= c with M[:, r, c] != 0
        col = M[:, :, c].copy()
        col[:, :c] = 0  # ignore rows above c (already pivoted)
        nz = (col % p) != 0
        # for each system, pick smallest row index r>=c that is nonzero
        # rows < c are zeroed so argmax of nz gives first True at >= c (if any True there)
        has = nz.any(axis=1)
        piv = np.argmax(nz, axis=1)  # first nonzero row index
        singular |= ~has
        # swap row c and row piv for systems with has
        idx = np.where(has)[0]
        if idx.size:
            r_c = M[idx, c, :].copy()
            r_p = M[idx, piv[idx], :].copy()
            M[idx, c, :] = r_p
            M[idx, piv[idx], :] = r_c
        # normalize pivot row c (only for non-singular-so-far systems)
        pivval = M[:, c, c] % p
        good = has & (pivval != 0)
        gidx = np.where(good)[0]
        if gidx.size:
            inv = np.array([pow(int(v), p-2, p) for v in pivval[gidx]], dtype=np.int64)
            M[gidx, c, :] = (M[gidx, c, :] * inv[:, None]) % p
            # eliminate column c from all other rows
            factors = M[gidx][:, :, c].copy()  # (g, s)
            factors[np.arange(gidx.size), c] = 0  # don't touch pivot row itself
            # M[g, r, :] -= factors[g,r] * M[g, c, :]
            sub = factors[:, :, None] * M[gidx, c, :][:, None, :]  # (g, s, s+1)
            M[gidx, :, :] = (M[gidx, :, :] - sub) % p
    x = M[:, :, s] % p
    return x, singular

def pencil_I(p, n, k, a, b, combos, powr, za, zb):
    # combos: (C, k+1) array of point-index subsets ; powr: (n,k) vandermonde cols x^0..x^{k-1}
    # za,zb: (n,) arrays = z^{i*a}, z^{i*b}
    C = combos.shape[0]
    s = k+1
    # build A: (C, s, s): [ powr[A] (k cols) | -za[A] (1 col) ] ; B = zb[A]
    sub = combos  # (C, s)
    Vsub = powr[sub]               # (C, s, k)
    zacol = (-za[sub]) % p         # (C, s)
    A = np.concatenate([Vsub, zacol[:, :, None]], axis=2)  # (C, s, k+1)
    B = zb[sub]                    # (C, s)
    x, singular = batch_solve_modp(A, B, p)  # x: (C, s) = (g_0..g_{k-1}, gamma)
    g = x[:, :k]      # (C, k)
    gamma = x[:, k]   # (C,)
    valid = ~singular
    if not valid.any():
        return {}
    g = g[valid]; gamma = gamma[valid]
    # evaluate g at all n points: gvals[c,i] = sum_j g[c,j]*powr[i,j]  mod p  -> (C', n)
    gvals = (g @ powr.T) % p          # (C', n)  ; powr.T (k, n)
    fvals = (zb[None, :] + gamma[:, None] * za[None, :]) % p  # (C', n)
    agree = (gvals == fvals).sum(axis=1)  # (C',) true agreement count
    # per distinct gamma keep max agreement
    best = {}
    gam_arr = gamma.tolist(); ag_arr = agree.tolist()
    for gm, ag in zip(gam_arr, ag_arr):
        if gm not in best or ag > best[gm]:
            best[gm] = ag
    # I(w) = #gamma with maxagree >= w
    Iw = {}
    vals = list(best.values())
    for w in range(k+1, n+1):
        Iw[w] = sum(1 for v in vals if v >= w)
    return Iw

def far_pencils(n, k, representative=False):
    fars = [x for x in range(k, n) if x != n//2]
    pairs = [(a, b) for a in fars for b in fars if a < b]
    if not representative:
        return pairs
    # representative subset: all coprime-diff pencils (gcd(b-a, n)==1) + several gcd>1 ones
    rep = []
    seen_gcd = {}
    for (a, b) in pairs:
        gg = math.gcd((b - a) % n if (b-a) % n else n, n)
        if gg == 1:
            rep.append((a, b))
        else:
            # keep up to 4 per gcd class to sample structured pencils
            seen_gcd.setdefault(gg, 0)
            if seen_gcd[gg] < 6:
                rep.append((a, b)); seen_gcd[gg] += 1
    return rep

def deltastar(n, k, p, representative=False, verbose=False):
    z = proot(p, n)
    pts = np.array([pow(z, i, p) for i in range(n)], dtype=np.int64)
    powr = np.array([[pow(int(pts[i]), j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    pairs = far_pencils(n, k, representative)
    combos = np.array(list(itertools.combinations(range(n), k+1)), dtype=np.int64)
    worst = {w: 0 for w in range(k+1, n+1)}
    worst_pencil = {w: None for w in range(k+1, n+1)}
    t0 = time.time()
    for idx, (a, b) in enumerate(pairs):
        za = np.array([pow(z, (i*a) % n, p) for i in range(n)], dtype=np.int64)
        zb = np.array([pow(z, (i*b) % n, p) for i in range(n)], dtype=np.int64)
        Iw = pencil_I(p, n, k, a, b, combos, powr, za, zb)
        for w, v in Iw.items():
            if v > worst[w]:
                worst[w] = v; worst_pencil[w] = (a, b)
        if verbose and (idx % max(1, len(pairs)//10) == 0):
            print(f"    pencil {idx+1}/{len(pairs)} (a,b)=({a},{b}) elapsed={time.time()-t0:.1f}s", flush=True)
    budget = n
    cross = None
    for w in range(k+1, n+1):
        if worst[w] <= budget:
            cross = w; break
    return worst, cross, worst_pencil, len(pairs)

def run(n, k, representative=False, verbose=False, pmult=4):
    want = (n**3) * pmult  # p >> n^3
    p = find_prime(n, want)
    assert isprime(p) and (p-1) % n == 0
    rho = k/n
    cap = 1 - rho
    john = 1 - math.sqrt(rho)
    npairs = math.comb(n-2 if n//2 in range(k,n) else n-1, 2)  # rough
    print(f"\n=== n={n} k={k} rho={rho:.4f} p={p} (p/n^3={p/n**3:.1f}) C(n,k+1)={math.comb(n,k+1):,} "
          f"far-pencils={'rep' if representative else 'all'} ===", flush=True)
    worst, cross, wp, np_used = deltastar(n, k, p, representative, verbose)
    band = [worst[w] for w in range(k+1, n+1)]
    dstar = 1 - cross/n if cross else None
    print(f"  pencils used={np_used}; worstI per band (w={k+1}..{n}): {band}")
    if cross is not None:
        gap = cap - dstar
        print(f"  budget=n={n}: crossing w_cross={cross} (worst pencil {wp[cross]}) -> delta*={dstar:.5f}")
        print(f"  w_cross-k={cross-k}  log2(n)={math.log2(n):.3f}  C_rho_est=(w-k)/log2(n)={(cross-k)/math.log2(n):.4f}")
        print(f"  n*(cap-delta*)={n*gap:.3f}  cap={cap:.4f} Johnson={john:.4f}")
        return dict(n=n, k=k, rho=rho, p=p, w_cross=cross, wmk=cross-k, log2n=math.log2(n),
                    dstar=dstar, cap=cap, gap=gap, Crho=(cross-k)/math.log2(n), pencil=wp[cross])
    else:
        print("  NO crossing within band (worstI never <= n) -> delta* below grid?")
        return dict(n=n, k=k, rho=rho, p=p, w_cross=None)

if __name__ == "__main__":
    results = []
    # cheap re-confirmations
    results.append(run(16, 2, representative=False))   # rho=1/8
    results.append(run(32, 4, representative=False))   # rho=1/8
    results.append(run(16, 4, representative=False))   # rho=1/4
    # rate-matched rho=1/16 ladder
    results.append(run(32, 2, representative=False))   # rho=1/16 n=32
    # rho=1/4 n=32 (k=8): C(32,9)=28M -> representative
    results.append(run(32, 8, representative=True, verbose=True))  # rho=1/4 n=32
    print("\n\n############ SUMMARY TABLE ############")
    print(f"{'rho':>7} {'n':>4} {'k':>3} {'w_cross':>8} {'w-k':>5} {'log2n':>6} {'C_rho':>7} {'delta*':>9} {'n*gap':>7}")
    for r in results:
        if r.get('w_cross') is None:
            print(f"{r['rho']:>7.4f} {r['n']:>4} {r['k']:>3}   NO-CROSS")
            continue
        print(f"{r['rho']:>7.4f} {r['n']:>4} {r['k']:>3} {r['w_cross']:>8} {r['wmk']:>5} {r['log2n']:>6.3f} {r['Crho']:>7.4f} {r['dstar']:>9.5f} {r['n*gap' if 'n*gap' in r else 'gap']*r['n'] if False else r['gap']*r['n']:>7.3f}")
    # save for n=64 (separate run due to time)
    print("\n(n=64 runs in probe_char0_deltastar_n64_BIG.py)")
