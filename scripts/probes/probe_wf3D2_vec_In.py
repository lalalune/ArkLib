#!/usr/bin/env python3
"""
wf-D2 (#444): VECTORIZED (numpy) far-line incidence — closed-form hunt to larger n.

Same exact object as probe_farline_incidence_exact.incidence, but:
  - precompute left-null bases for all size-s witness sets ONCE, stack into int64 arrays
    P[W, c, s] (c = codim = s-k, constant for non-degenerate sets) and Ridx[W, s];
  - per direction (a,b): gather, batched modular matvec, vectorized single-gamma solve.
This reaches n=24 (s-k=2: C(24,8)=735k) and n=32 (s-k=2: C(32,10)=64M is still too big, so we
report n=24 and use n<=24 + GPU n=16..38 for the closed form).

All modular arithmetic in int64 with periodic % p (products bounded by p^2 ~ (2e5)^2 < 2^63). OK.
"""
import sys, itertools, argparse
sys.path.insert(0, 'scripts/probes')
import numpy as np
from collections import Counter
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W


def left_null_rows(V, p):
    m = len(V); k = len(V[0]) if m else 0
    rows = [list(V[i]) + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    nc = k + m; pr = 0
    for c in range(k):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    out = []
    for row in rows:
        if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:]):
            out.append([row[k + j] % p for j in range(m)])
    return out


def build(S, p, k, s):
    """Return Ridx (W,s) int, P (W,c,s) int64, for all non-degenerate codim-c=s-k witness sets."""
    n = len(S); c = s - k
    Ridx = []; Pmats = []
    for R in itertools.combinations(range(n), s):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null_rows(V, p)
        if len(P) != c:
            continue
        Ridx.append(R); Pmats.append(P)
    if not Ridx:
        return None, None
    return np.array(Ridx, dtype=np.int64), np.array(Pmats, dtype=np.int64)


def incidence_vec(ua, ub, Ridx, P, p):
    """ua,ub: length-n int arrays. Returns (#distinct gamma, gamma_multiplicity_counter)."""
    W, c, s = P.shape
    uaR = ua[Ridx]  # W,s
    ubR = ub[Ridx]
    # pa[w,t] = sum_i P[w,t,i]*uaR[w,i]  mod p
    pa = np.einsum('wts,ws->wt', P, uaR) % p   # W,c
    pb = np.einsum('wts,ws->wt', P, ubR) % p
    # per witness: pa + gamma pb = 0 (all c comps). Use first nonzero pb component.
    nz = pb != 0  # W,c
    has_b = nz.any(axis=1)  # W
    # heavy: pb all zero. If also pa all zero -> saturated (return p).
    heavy = ~has_b
    if heavy.any():
        pa_heavy_zero = (pa[heavy] == 0).all(axis=1)
        if pa_heavy_zero.any():
            return p, None  # saturated
    # for has_b witnesses: first nonzero index
    res = {}
    idx = np.where(has_b)[0]
    if len(idx) == 0:
        return 0, Counter()
    pbb = pb[idx]; paa = pa[idx]
    first = np.argmax(pbb != 0, axis=1)  # first nonzero per row
    rows = np.arange(len(idx))
    pb_first = pbb[rows, first]
    pa_first = paa[rows, first]
    # gamma = -pa_first * inv(pb_first)
    inv = np.array([pow(int(x), p - 2, p) for x in pb_first], dtype=np.int64)
    gamma = (-pa_first * inv) % p  # len idx
    # verify all components: pa + gamma*pb == 0
    check = (paa + gamma[:, None] * pbb) % p
    valid = (check == 0).all(axis=1)
    gvalid = gamma[valid]
    cnt = Counter(int(g) for g in gvalid)
    return len(cnt), cnt


def mono_arr(b, S, p):
    return np.array([pow(int(x), b, p) for x in S], dtype=np.int64)


def run(n, k, s, p, b_range=None):
    S = list(get_W(n, p).S)
    Ridx, P = build(S, p, k, s)
    if Ridx is None:
        print(f"n={n} k={k} s={s}: no non-degenerate sets", flush=True); return None
    W = Ridx.shape[0]
    b_range = b_range or range(k, s)
    best = (-1, None, None)
    for b in b_range:
        ub = mono_arr(b, S, p)
        for a in range(n):
            if a == b: continue
            ua = mono_arr(a, S, p)
            I, cnt = incidence_vec(ua, ub, Ridx, P, p)
            if p > I > best[0]:
                best = (I, (a, b), cnt)
    I, d, cnt = best
    hist = dict(Counter(sorted(cnt.values(), reverse=True))) if cnt else {}
    print(f"n={n} k={k} s={s} (s-k={s-k}) #nulls={W} budget={n}: maxI={I} dir={d} hist={hist}", flush=True)
    return I, d, hist


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', type=str, default='8:2:4,16:4:6,24:6:8',
                    help='comma list n:k:s')
    ap.add_argument('--prime', type=int, default=200003)
    args = ap.parse_args()
    for case in args.cases.split(','):
        n, k, s = (int(x) for x in case.split(':'))
        p = find_prime_cong1(n, args.prime)
        run(n, k, s, p)
    print("DONE", flush=True)
