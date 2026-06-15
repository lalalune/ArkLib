#!/usr/bin/env python3
"""
wf-D1 (#444): FAST vectorized wf-NH binding far-line incidence I(n) -> n=32 FULL, n=64 reach.

THE decisive computation. wf-NH object (FarCosetExplosion exact, axiom-clean), k=4, size=k+2=6
(s-k=2, the OVER-DETERMINED binding regime), far b in [k, size):
  for far dir u1=x^b, offset u0=x^a over mu_n in F_p, agreement size s=6, r=n-6:
    I(a,b) = #{ gamma in F_p : x^a + gamma x^b agrees with RS[k] on >= s points }
  Per agreement set R (|R|=6): condition u0|_R + gamma u1|_R in col(V_R) (V_R = 6x4 Vandermonde).
  Since rank V_R = 4, this is rank[V_R | u]=4 <=> all six 5x5 minors det[1,x,x^2,x^3,u | T]
  vanish, T the 5-subsets of R. Each minor is AFFINE in gamma (u=u0+gamma u1):
     D_T(u0) + gamma D_T(u1) = 0.
  R contributes a single gamma g_R iff all six 5-subset minors are consistent (heavy if all
  D_T(u1)=0 too). I = p if any heavy-and-u0-also-vanishes else |{g_R}|.

KEY VECTORIZATION (cofactor factorization): expand each 5x5 minor along the last (u) column:
   D_T(x^e) = sum_{j in T} sign(j,T) * x^e[j] * Minor4(T\{j})
where Minor4(.) = 4x4 Vandermonde det of the other 4 points (INDEPENDENT of e). Precompute, per p,
the cofactor weight  w[T][j] = sign * Minor4(T\{j})  for every 5-subset T (ONCE). Then for any
direction e,  D_T(x^e) = sum_j w[T][j] x^e[j]  is a single batched matmul over all 5-subsets.
Then assemble per 6-subset from its six 5-subsets. All numpy, all exact mod p.

Cross-check: n=16 must reproduce delta*=9/16 binder (a=10,b=4) I=89, p-independent.
"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1, incidence as ref_incidence
from prize_workspace import get_W

K = 4
SIZE = 6  # = k+2, s-k=2 over-determined binding regime


def vander_det4(pts, p):
    """4x4 Vandermonde det of 4 field points (product of differences) mod p."""
    d = 1
    m = len(pts)
    for i in range(m):
        for j in range(i+1, m):
            d = (d * ((pts[j] - pts[i]) % p)) % p
    return d % p


def build_cofactors(S, p):
    """For every 5-subset T of [n], precompute weight vector over its 5 members:
       w_T[t] = (-1)^(pos of column) * Vandermonde4(T without member t).
       Returns: fives (list of 5-tuples), Wmat (numpy (#fives,5) int64) aligned to T order.
    """
    n = len(S)
    Sarr = [int(x) % p for x in S]
    fives = list(itertools.combinations(range(n), 5))
    W = np.zeros((len(fives), 5), dtype=np.int64)
    for ti, T in enumerate(fives):
        for t in range(5):
            others = [Sarr[T[u]] for u in range(5) if u != t]
            # 5x5 det expanded along last column, row = t. Sign (-1)^(t + 4) for last col (idx4, 0-based)
            sign = (-1) ** (t + 4)
            W[ti, t] = (sign * vander_det4(others, p)) % p
    return fives, W, np.array(Sarr, dtype=np.int64)


def five_index(n):
    """Map each 6-subset to indices of its six 5-subsets within the fives enumeration, plus the
       member-position alignment so we can gather the right column from Wmat."""
    fives = list(itertools.combinations(range(n), 5))
    pos = {T: i for i, T in enumerate(fives)}
    sixes = list(itertools.combinations(range(n), 6))
    # For each six R, its six 5-subsets are R\{R[m]} for m in 0..5.
    six2five = np.zeros((len(sixes), 6), dtype=np.int64)
    for ri, R in enumerate(sixes):
        for m in range(6):
            T = tuple(R[u] for u in range(6) if u != m)
            six2five[ri, m] = pos[T]
    return sixes, six2five


def D_for_dir(Wmat, fives_arr, monodir, p):
    """D_T(x^e) for all 5-subsets T: sum_t Wmat[T,t] * x^e[T[t]] mod p.
       fives_arr: (#fives,5) int64 of member point-indices; monodir: length-n x^e values."""
    vals = monodir[fives_arr]            # (#fives,5)
    return (Wmat * vals).sum(axis=1) % p


def incidence_dir(monos_a, monos_b, Wmat, fives_arr, six2five, p):
    """Vectorized incidence for direction (u0=x^a -> monos_a, u1=x^b -> monos_b)."""
    D0 = D_for_dir(Wmat, fives_arr, monos_a, p)   # per 5-subset
    D1 = D_for_dir(Wmat, fives_arr, monos_b, p)
    A = D0[six2five]   # (#sixes,6)
    B = D1[six2five]
    # For each six: heavy if all B==0. If heavy & all A==0 -> saturated (return p).
    Bz = (B == 0)
    allBz = Bz.all(axis=1)
    if allBz.any():
        Az = (A == 0)
        if (allBz & Az.all(axis=1)).any():
            return p, True
    # Non-heavy rows: pick a column with B!=0, gamma = -A/B; require consistency across all 6.
    # gamma_col = -A * inv(B) where B!=0; rows where ALL six minors give same gamma -> contribute.
    # Strategy: compute candidate gamma from first nonzero B column; verify A + gamma*B == 0 for all.
    Bnz = ~Bz
    has = Bnz.any(axis=1)
    rows = np.nonzero(has)[0]
    good = set()
    if rows.size:
        Bsub = B[rows]; Asub = A[rows]; Bnzsub = Bnz[rows]
        first = Bnzsub.argmax(axis=1)
        ar = np.arange(rows.size)
        bb = Bsub[ar, first] % p
        aa = Asub[ar, first] % p
        binv = np.array([pow(int(x), p-2, p) for x in bb], dtype=np.int64)
        gam = (-aa * binv) % p
        # verify A + gam*B == 0 across all 6 columns
        check = (Asub + gam[:, None] * Bsub) % p
        ok = (check == 0).all(axis=1)
        for g in gam[ok]:
            good.add(int(g))
    return len(good), False


def max_far_incidence(n, p, a_full=True):
    S = list(get_W(n, p).S)
    fives, Wmat, Sarr = build_cofactors(S, p)
    fives_arr = np.array(fives, dtype=np.int64)
    sixes, six2five = five_index(n)
    def mono(e):
        return np.array([pow(int(Sarr[i]), e, p) for i in range(n)], dtype=np.int64)
    monos = {e: mono(e) for e in range(max(n, SIZE))}
    best = (-1, None)
    a_range = range(n) if a_full else range(min(n, 16))
    for b in range(K, SIZE):  # far condition: b in [k, size)
        for a in a_range:
            if a == b:
                continue
            I, sat = incidence_dir(monos[a], monos[b], Wmat, fives_arr, six2five, p)
            if not sat and I > best[0]:
                best = (I, (a, b))
    return best, len(sixes)


def run(n, primes, a_full=True):
    r = n - SIZE
    print(f"\n=== n={n} k={K} size={SIZE} (s-k=2) r={r} delta={r/n:.4f} budget={n} ===", flush=True)
    vals = []
    for plo in primes:
        p = find_prime_cong1(n, plo)
        t = time.time()
        (I, dirn), nsix = max_far_incidence(n, p, a_full=a_full)
        vals.append(I)
        tag = "GOOD(<=budget)" if I <= n else "BAD(>budget)"
        print(f"  p={p:>10}: maxI={I} dir={dirn} [{tag}]  (#6-sets={nsix}, {time.time()-t:.1f}s)", flush=True)
    pind = len(set(vals)) == 1
    print(f"  -> I({n}) p-INDEPENDENT: {pind}; vals={vals}", flush=True)
    return vals


def selfcheck_n16():
    """Cross-check vectorized engine vs the proven reference incidence() at n=16."""
    p = find_prime_cong1(16, 200003)
    S = list(get_W(16, p).S)
    (I, dirn), _ = max_far_incidence(16, p, a_full=True)
    # reference: scan same far directions
    rbest = (-1, None)
    r = 16 - SIZE
    for b in range(K, SIZE):
        for a in range(16):
            if a == b: continue
            c, _ = ref_incidence(S, p, K, a, b, r)
            if c > rbest[0]: rbest = (c, (a, b))
    print(f"[selfcheck n=16] vectorized maxI={I} dir={dirn} | reference maxI={rbest[0]} dir={rbest[1]} | MATCH={I==rbest[0]}", flush=True)
    return I == rbest[0]


if __name__ == '__main__':
    args = sys.argv[1:] or ['check', '16', '32']
    if 'check' in args:
        ok = selfcheck_n16()
        if not ok:
            print("SELFCHECK FAILED -- aborting", flush=True); sys.exit(1)
    if '16' in args:
        run(16, [200003, 5000011, 16777259])
    if '32' in args:
        run(32, [1048609, 1048897])   # prize-scale p~n^4, two primes for p-independence
    if '64' in args:
        # C(64,6)=75M, C(64,5)=7.6M cofactors. a_full sweeps 64 offsets x 2 far b. Direction-limited
        # if too slow: a_full=False (16 offsets). One prize-scale prime.
        run(64, [16777259], a_full=(len(args) > 0 and 'afull' in args))
    print("DONE", flush=True)
