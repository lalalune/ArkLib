#!/usr/bin/env python3
"""
wf-D1 (#444): n=64 binding wf-NH incidence I(64) -- memory-lean, chunked, vectorized cofactors.

Same exact object as probe_wf3D1_fast_incidence (k=4, size=6, far b in [k,size), s-k=2), but:
  - cofactor weights w_T[t] for all C(64,5)=7.6M 5-subsets built with VECTORIZED Vandermonde dets,
  - six-subsets streamed in chunks (C(64,6)=75M) so we never hold the full 75M x 6 index array,
  - one prize-scale prime (I is p-independent: PROVEN at n=16,32), a-sweep configurable.

Validated against probe_wf3D1_fast_incidence at n=16 (--check).
"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W

K = 4
SIZE = 6


def build_cofactors_vec(Sarr, p):
    """Vectorized cofactor weights for all 5-subsets T:
       w_T[t] = (-1)^(t+4) * Vandermonde4(T \ {T[t]})   (5x5 minor expanded along u-column).
       Returns fives (np int64 (#fives,5) of point INDICES) and W (np int64 (#fives,5))."""
    n = len(Sarr)
    # MUST be COLEX order so the combinatorial-number-system rank in _five_rank_vec
    # (sum_t C(c_t, t+1)) indexes these correctly.
    fl = sorted(itertools.combinations(range(n), 5), key=lambda T: [T[i] for i in range(4, -1, -1)])
    fives = np.array(fl, dtype=np.int64)                                         # (F,5) indices, colex
    pts = Sarr[fives] % p                                                        # (F,5) field values
    F = fives.shape[0]
    W = np.empty((F, 5), dtype=np.int64)
    sign = np.array([(-1) ** (t + 4) for t in range(5)], dtype=np.int64)
    # Vandermonde4 of the 4 points other than position t = product over i<j (both != t) of (pj - pi)
    cols = list(range(5))
    for t in range(5):
        others = [c for c in cols if c != t]  # 4 columns
        d = np.ones(F, dtype=np.int64)
        for ii in range(4):
            for jj in range(ii + 1, 4):
                d = (d * ((pts[:, others[jj]] - pts[:, others[ii]]) % p)) % p
        W[:, t] = (sign[t] * d) % p
    return fives, W


def comb_rank_maps(n):
    """Helper: enumerate 5-subsets to build a rank dict for mapping 6-subset -> its 5-subset ids.
       We DON'T store the 75M map; we recompute per chunk. Returns a dict {5-tuple: id}."""
    return {T: i for i, T in enumerate(itertools.combinations(range(n), 5))}


def incidence_dir_chunked(monos_a, monos_b, fives, W, five_rank, n, p, chunk=2_000_000):
    """Streamed incidence for one direction. Computes D0,D1 per 5-subset once, then streams
       6-subsets in chunks mapping each to its six 5-subset ids."""
    va = monos_a[fives]              # (F,5)
    vb = monos_b[fives]
    D0 = (W * va).sum(axis=1) % p    # (F,)
    D1 = (W * vb).sum(axis=1) % p
    good = set()
    saturated = False
    six_iter = itertools.combinations(range(n), 6)
    inv_cache = {}
    while True:
        block = list(itertools.islice(six_iter, chunk))
        if not block:
            break
        B6 = np.array(block, dtype=np.int64)            # (C,6) point indices
        C = B6.shape[0]
        # six 5-subset ids per row: drop column m
        ids = np.empty((C, 6), dtype=np.int64)
        for m in range(6):
            keep = [c for c in range(6) if c != m]
            sub = B6[:, keep]                            # (C,5) sorted (since B6 rows sorted)
            # rank lookup vectorized via dict on tuples is slow; use combinatorial number system.
            ids[:, m] = _five_rank_vec(sub, n)
        A = D0[ids]; Bm = D1[ids]                        # (C,6)
        Bz = (Bm == 0)
        allBz = Bz.all(axis=1)
        if allBz.any():
            Az = (A == 0)
            if (allBz & Az.all(axis=1)).any():
                return p, True
        Bnz = ~Bz
        has = Bnz.any(axis=1)
        idxr = np.nonzero(has)[0]
        if idxr.size:
            Asub = A[idxr]; Bsub = Bm[idxr]; Bnzsub = Bnz[idxr]
            first = Bnzsub.argmax(axis=1)
            ar = np.arange(idxr.size)
            bb = Bsub[ar, first] % p
            aa = Asub[ar, first] % p
            binv = np.empty(bb.shape, dtype=np.int64)
            for i in range(bb.shape[0]):
                v = int(bb[i])
                iv = inv_cache.get(v)
                if iv is None:
                    iv = pow(v, p - 2, p); inv_cache[v] = iv
                binv[i] = iv
            gam = (-aa * binv) % p
            check = (Asub + gam[:, None] * Bsub) % p
            ok = (check == 0).all(axis=1)
            for g in gam[ok]:
                good.add(int(g))
    return len(good), saturated


def _binom(n, k):
    from math import comb
    return comb(n, k)


def _five_rank_vec(sub, n):
    """Combinatorial number system rank of sorted 5-subsets (rows of `sub`, each strictly increasing).
       rank = sum_{t=0}^{4} C(sub[t], t+1)."""
    from math import comb
    C = sub.shape[0]
    out = np.zeros(C, dtype=np.int64)
    for t in range(5):
        col = sub[:, t]
        # C(col, t+1) vectorized via lookup table over 0..n-1
        table = np.array([comb(int(v), t + 1) for v in range(n)], dtype=np.int64)
        out += table[col]
    return out


def max_far_incidence(n, p, a_full=True, chunk=2_000_000):
    S = list(get_W(n, p).S)
    Sarr = np.array([int(x) for x in S], dtype=np.int64)
    t0 = time.time()
    fives, W = build_cofactors_vec(Sarr, p)
    print(f"    [cofactors built: {fives.shape[0]} 5-subsets, {time.time()-t0:.1f}s]", flush=True)
    def mono(e):
        return np.array([pow(int(Sarr[i]), e, p) for i in range(n)], dtype=np.int64)
    monos = {e: mono(e) for e in range(max(n, SIZE))}
    best = (-1, None)
    a_range = range(n) if a_full else list(range(min(n, 16)))
    for b in range(K, SIZE):
        for a in a_range:
            if a == b:
                continue
            ti = time.time()
            I, sat = incidence_dir_chunked(monos[a], monos[b], fives, W, None, n, p, chunk)
            if not sat and I > best[0]:
                best = (I, (a, b))
            print(f"    dir(a={a},b={b}): I={I} sat={sat}  ({time.time()-ti:.1f}s)  best={best}", flush=True)
    return best


def selfcheck():
    from probe_wf3D1_fast_incidence import max_far_incidence as ref_max
    p = find_prime_cong1(16, 200003)
    (Ir, dr), _ = ref_max(16, p, a_full=True)
    (I2, d2) = max_far_incidence(16, p, a_full=True)
    print(f"[n=64-engine selfcheck @ n=16] ref maxI={Ir} dir={dr} | streamed maxI={I2} dir={d2} | MATCH={Ir==I2}", flush=True)
    return Ir == I2


if __name__ == '__main__':
    args = sys.argv[1:]
    if 'check' in args or not args:
        if not selfcheck():
            print("SELFCHECK FAILED", flush=True); sys.exit(1)
    if '64' in args:
        afull = 'afull' in args
        p = find_prime_cong1(64, 16777259)  # ~n^4
        r = 64 - SIZE
        print(f"\n=== n=64 k=4 size=6 r={r} delta={r/64:.4f} budget=64 p={p} a_full={afull} ===", flush=True)
        t = time.time()
        I, dirn = max_far_incidence(64, p, a_full=afull)
        print(f"  => I(64) = {I} dir={dirn}  [{'GOOD' if I<=64 else 'BAD'}]  ({time.time()-t:.0f}s total)", flush=True)
    print("DONE", flush=True)
