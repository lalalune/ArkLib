#!/usr/bin/env python3
"""
wf-D1 (#444): UNIFIED fast vectorized wf-NH binding incidence I(n), n=16/32/64.

Object (= FarCosetExplosion exact, axiom-clean), k=4, size=6 (s-k=2 over-determined binding):
  far dir u1=x^b (b in [4,6)), offset u0=x^a, agreement size 6, r=n-6, budget=n.
  I(a,b)=#{gamma: x^a+gamma x^b agrees with RS[4] on >=6 pts} (per-set <=1 gamma; FarCoset law).

Per 6-subset R: u|_R in col(V_R) (6x4 Vandermonde, rank 4) <=> all six 5x5 minors
det[1,x,x^2,x^3,u | T]=0 over its 5-subsets T. Each minor affine in gamma. Cofactor expand along
u-column: D_T(x^e)=sum_t w_T[t] x^e[T[t]], w_T[t]=(-1)^(t+4) Vandermonde4(T\{T[t]}).

VECTORIZED EVERYWHERE:
  - 5-subsets generated in COLEX order via numpy (no Python sort).
  - cofactor Vandermonde4 dets fully numpy.
  - 6-subsets streamed via numpy chunks; each 6-subset's six 5-subset COLEX ranks via CNS
    rank = sum_t C(c_t, t+1) (pure vectorized arithmetic, matches colex generation).
Validated against proven `incidence` reference at n=16 (I=89, dir (10,4), p-independent).
"""
import sys, time
import numpy as np
from math import comb
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1, incidence as ref_incidence
from prize_workspace import get_W

K = 4
SIZE = 6


def colex_combinations(n, k):
    """All k-subsets of range(n) in COLEX order as a numpy (C,k) int array, fully vectorized.
       Colex order: sort by last coord, then 2nd-last, ... Equivalent to ascending CNS rank."""
    # Generate via recursive numpy stacking on the highest index.
    if k == 0:
        return np.zeros((1, 0), dtype=np.int64)
    out = []
    # colex: for fixed top element t (= largest), the rest is a (k-1)-subset of range(t).
    # Iterating t ascending and recursing gives ascending colex rank.
    for t in range(k - 1, n):
        sub = colex_combinations(t, k - 1)  # subsets of range(t)
        if sub.shape[0] == 0:
            continue
        col = np.full((sub.shape[0], 1), t, dtype=np.int64)
        out.append(np.concatenate([sub, col], axis=1))
    return np.concatenate(out, axis=0) if out else np.zeros((0, k), dtype=np.int64)


def cns_rank(sub, k):
    """Colex CNS rank of sorted k-subsets (rows ascending): sum_t C(sub[:,t], t+1)."""
    nmax = int(sub.max()) + 1 if sub.size else 1
    out = np.zeros(sub.shape[0], dtype=np.int64)
    for t in range(k):
        table = np.array([comb(v, t + 1) for v in range(nmax)], dtype=np.int64)
        out += table[sub[:, t]]
    return out


def build_cofactors(Sarr, p):
    """fives (colex, (F,5) point-index), W ((F,5) cofactor weights) mod p, fully vectorized."""
    n = len(Sarr)
    fives = colex_combinations(n, 5)
    pts = Sarr[fives] % p
    F = fives.shape[0]
    W = np.empty((F, 5), dtype=np.int64)
    for t in range(5):
        others = [c for c in range(5) if c != t]
        d = np.ones(F, dtype=np.int64)
        for ii in range(4):
            for jj in range(ii + 1, 4):
                d = (d * ((pts[:, others[jj]] - pts[:, others[ii]]) % p)) % p
        sign = (-1) ** (t + 4)
        W[:, t] = (sign * d) % p
    return fives, W


def incidence_dir(D0, D1, sixes_chunks_iter, p, inv_cache):
    """Given per-5-subset D0,D1 arrays and an iterator of (six2five_id) chunks, return (I, sat)."""
    good = set()
    for ids in sixes_chunks_iter:   # ids: (C,6) colex ranks of the six 5-subsets
        A = D0[ids]; Bm = D1[ids]
        Bz = (Bm == 0)
        allBz = Bz.all(axis=1)
        if allBz.any():
            if (allBz & (A == 0).all(axis=1)).any():
                return p, True
        Bnz = ~Bz
        has = Bnz.any(axis=1)
        idxr = np.nonzero(has)[0]
        if idxr.size:
            Asub = A[idxr]; Bsub = Bm[idxr]
            first = Bnz[idxr].argmax(axis=1)
            ar = np.arange(idxr.size)
            bb = Bsub[ar, first] % p
            aa = Asub[ar, first] % p
            binv = np.empty(bb.shape, dtype=np.int64)
            for i in range(bb.shape[0]):
                v = int(bb[i]); iv = inv_cache.get(v)
                if iv is None:
                    iv = pow(v, p - 2, p); inv_cache[v] = iv
                binv[i] = iv
            gam = (-aa * binv) % p
            ok = ((Asub + gam[:, None] * Bsub) % p == 0).all(axis=1)
            good.update(int(g) for g in gam[ok])
    return len(good), False


def make_six_id_chunks(n, chunk):
    """Yield chunks of (C,6) arrays giving the colex ranks of the six 5-subsets of each 6-subset.
       6-subsets enumerated in colex; for each we drop one of 6 columns and CNS-rank the 5-subset."""
    sixes = colex_combinations(n, 6)   # (S,6)
    S = sixes.shape[0]
    for start in range(0, S, chunk):
        block = sixes[start:start + chunk]
        C = block.shape[0]
        ids = np.empty((C, 6), dtype=np.int64)
        for m in range(6):
            keep = [c for c in range(6) if c != m]
            ids[:, m] = cns_rank(block[:, keep], 5)
        yield ids


def max_far_incidence(n, p, a_full=True, chunk=3_000_000, verbose=False):
    S = list(get_W(n, p).S)
    Sarr = np.array([int(x) for x in S], dtype=np.int64)
    t0 = time.time()
    fives, W = build_cofactors(Sarr, p)
    # Precompute the six-id chunks ONCE (reused for all directions) as a list (memory permitting).
    six_chunks = list(make_six_id_chunks(n, chunk))
    if verbose:
        print(f"    [setup: {fives.shape[0]} 5-subsets, {sum(c.shape[0] for c in six_chunks)} 6-subsets, {time.time()-t0:.1f}s]", flush=True)
    def mono(e):
        return np.array([pow(int(Sarr[i]), e, p) for i in range(n)], dtype=np.int64)
    monos = {e: mono(e) for e in range(max(n, SIZE))}
    inv_cache = {}
    best = (-1, None)
    a_range = range(n) if a_full else range(min(n, 16))
    for b in range(K, SIZE):
        vb = monos[b][fives]
        D1 = (W * vb).sum(axis=1) % p
        for a in a_range:
            if a == b:
                continue
            va = monos[a][fives]
            D0 = (W * va).sum(axis=1) % p
            I, sat = incidence_dir(D0, D1, six_chunks, p, inv_cache)
            if not sat and I > best[0]:
                best = (I, (a, b))
                if verbose:
                    print(f"      new best I={I} dir=(a={a},b={b})  ({time.time()-t0:.0f}s)", flush=True)
    return best


def selfcheck():
    p = find_prime_cong1(16, 200003)
    S = list(get_W(16, p).S)
    (I, dirn) = max_far_incidence(16, p, a_full=True)
    rbest = (-1, None)
    for b in range(K, SIZE):
        for a in range(16):
            if a == b: continue
            c, _ = ref_incidence(S, p, K, a, b, 16 - SIZE)
            if c > rbest[0]: rbest = (c, (a, b))
    ok = (I == rbest[0])
    print(f"[selfcheck n=16] unified maxI={I} dir={dirn} | reference maxI={rbest[0]} dir={rbest[1]} | MATCH={ok}", flush=True)
    return ok


def run(n, primes, a_full=True, chunk=3_000_000):
    r = n - SIZE
    print(f"\n=== n={n} k={K} size={SIZE} (s-k=2) r={r} delta={r/n:.4f} budget={n} a_full={a_full} ===", flush=True)
    vals = []
    for plo in primes:
        p = find_prime_cong1(n, plo)
        t = time.time()
        (I, dirn) = max_far_incidence(n, p, a_full=a_full, chunk=chunk, verbose=True)
        vals.append(I)
        tag = "GOOD(<=n)" if I <= n else "BAD(>n)"
        print(f"  p={p:>10}: I({n})={I} dir={dirn} [{tag}]  ({time.time()-t:.0f}s)", flush=True)
    if len(vals) > 1:
        print(f"  -> I({n}) p-INDEPENDENT: {len(set(vals))==1}; vals={vals}", flush=True)
    return vals


if __name__ == '__main__':
    args = sys.argv[1:] or ['check', '16', '32']
    if 'check' in args:
        if not selfcheck():
            print("SELFCHECK FAILED", flush=True); sys.exit(1)
    if '16' in args:
        run(16, [200003, 5000011, 16777259])
    if '32' in args:
        run(32, [1048609, 1048897])
    if '64' in args:
        afull = 'afull' in args
        run(64, [16777259], a_full=afull, chunk=4_000_000)
    print("DONE", flush=True)
