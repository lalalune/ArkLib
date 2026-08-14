#!/usr/bin/env python3
"""
probe_407_regimeB_sstar_np.py  (#444, wf-D2 regime-B residual) -- NUMPY VECTORIZED

Resolves the explicitly-flagged OPEN SUB-QUESTION (wf-D2 push e48d5ef59): regime A (n=16..28)
binding s* = n/2-1 (delta*=1/2+1/n -> Johnson); regime B (n>=32, GPU) "s* PINS at 13 across
n=32,34,38 ... MAY BE REAL ... THE GENUINE OPEN SUB-QUESTION." The GPU enumerated size-s witness
sets (infeasible) and timed out n>=36.

Here: rho=1/4 FIXED (k=n/4, the wf-D2 axis). EXACT incidence via the (k+1)-subset candidate-alpha
fact, then max-agreement per candidate computed with a NUMPY-VECTORIZED Lagrange evaluation over
all n domain points at once, and the C(n,k) k-subset max taken with early structure. budget=n.

  s* = max { thr : max_over_far_dirs I(b=k,a; thr) <= budget = n }.

Prize-faithful: PROPER mu_n (m=(p-1)/n>1), p>>n^3, p==1 mod n, NEVER n=q-1. Multi-prime. Exact
integer mod-p (numpy int64 with careful reduction; p < 2^31 so products fit int64). Python+numpy
=> axiom-clean trivially.
"""
import sys, itertools, argparse
from math import gcd, sqrt
import numpy as np


def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True


def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while not (is_prime(p) and (p - 1) % n == 0):
        p += n
    return p


def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p - 1) // n, p)
        if pow(w, n, p) == 1 and all(pow(w, n // q, p) != 1 for q in (2, 3, 5, 7) if n % q == 0):
            return w
    raise RuntimeError


def inv(a, p):
    return pow(int(a) % p, p - 2, p)


def alpha_for_subset(Tvals, a, b, p, k):
    Xs = Tvals
    m = k + 1
    M = [[pow(Xs[c], i, p) for c in range(m)] for i in range(k)]
    rows = [r[:] for r in M]
    pivots = []
    r = 0
    for c in range(m):
        piv = None
        for rr in range(r, k):
            if rows[rr][c] % p != 0:
                piv = rr; break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c], p)
        rows[r] = [(xx * iv) % p for xx in rows[r]]
        for rr in range(k):
            if rr != r and rows[rr][c] % p != 0:
                f = rows[rr][c]
                rows[rr] = [(aa - f * bb) % p for aa, bb in zip(rows[rr], rows[r])]
        pivots.append(c); r += 1
    free = [c for c in range(m) if c not in pivots]
    if not free:
        return None
    fc = free[0]
    lam = [0] * m
    lam[fc] = 1
    for i, c in enumerate(pivots):
        lam[c] = (-rows[i][fc]) % p
    U = sum(lam[c] * pow(Xs[c], a, p) for c in range(m)) % p
    V = sum(lam[c] * pow(Xs[c], b, p) for c in range(m)) % p
    if V % p == 0:
        return None
    return (-U * inv(V, p)) % p


def precompute_lagrange(n, k, p, X):
    """For each k-subset S of domain indices, precompute the n x k matrix L[S] where
    (L[S] @ y[S]) mod p = the deg<k interpolant through S evaluated at ALL n domain points.
    Returns list of (subset_tuple, L) with L an (n,k) int64 array mod p."""
    Xarr = [int(x) for x in X]
    out = []
    for S in itertools.combinations(range(n), k):
        bx = [Xarr[i] for i in S]
        L = np.zeros((n, k), dtype=np.int64)
        for jx in range(n):
            xx = Xarr[jx]
            for jj in range(k):
                num = 1; den = 1; xj = bx[jj]
                for ll in range(k):
                    if ll != jj:
                        num = num * ((xx - bx[ll]) % p) % p
                        den = den * ((xj - bx[ll]) % p) % p
                L[jx, jj] = num * inv(den, p) % p
        out.append((S, L))
    return out


def max_agree_vec(y_mat, lagr, p):
    """y_mat: (C, n) int64 array of C candidate words mod p.
    Returns (C,) int64 max agreement of each word with RS[k] (over all precomputed k-subsets)."""
    C = y_mat.shape[0]
    best = np.zeros(C, dtype=np.int64)
    for (S, L) in lagr:
        ys = y_mat[:, list(S)]                       # (C, k)
        # interpolant at all n points: (C, n) = ys @ L^T mod p
        interp = (ys @ L.T) % p                       # (C, n)
        agree = (interp == y_mat).sum(axis=1)         # (C,)
        best = np.maximum(best, agree)
    return best


def run(n, k, mults):
    budget = n
    rho = k / n
    print(f"=== n={n} k={k} rho={rho:.4f} budget=n={budget} "
          f"Johnson_thr~{sqrt(rho)*n:.2f} regimeA_pred_s*={n//2-1} ===", flush=True)
    for mult in mults:
        p = prime_ge(mult * n ** 3, n)
        w = find_gen(p, n)
        X = [pow(w, j, p) for j in range(n)]
        m_index = (p - 1) // n
        assert m_index > 1
        lagr = precompute_lagrange(n, k, p, X)
        per_thr_maxI = {}
        b = k
        seen_gcd = {}
        for a in range(k, n):
            if a == b: continue
            d = gcd((b - a) % n, n)
            if d not in seen_gcd:
                seen_gcd[d] = a
        for d, a in sorted(seen_gcd.items()):
            cand = set()
            Xl = [int(x) for x in X]
            for Tidx in itertools.combinations(range(n), k + 1):
                al = alpha_for_subset([Xl[j] for j in Tidx], a, b, p, k)
                if al is not None:
                    cand.add(al)
            cand = list(cand)
            if not cand:
                continue
            Xa = np.array([pow(int(x), a, p) for x in X], dtype=np.int64)
            Xb = np.array([pow(int(x), b, p) for x in X], dtype=np.int64)
            calp = np.array(cand, dtype=np.int64).reshape(-1, 1)
            y_mat = (Xa.reshape(1, -1) + (calp * Xb.reshape(1, -1)) % p) % p   # (C, n)
            agrs = max_agree_vec(y_mat, lagr, p)
            for thr in range(k + 1, n + 1):
                I = int((agrs >= thr).sum())
                cur = per_thr_maxI.get(thr)
                if cur is None or I > cur[0]:
                    per_thr_maxI[thr] = (I, (a, b, d))
        sstar = None
        for thr in range(n, k, -1):
            if per_thr_maxI.get(thr, (0, None))[0] <= budget:
                # binding s*: largest thr with maxI<=budget such that thr-1 is OVER OR thr is the
                # top of the contiguous OK band just above the explosion. We report the standard
                # wf-D2 s* = largest thr whose maxI<=budget AND maxI(thr-1) explodes (>budget).
                below = per_thr_maxI.get(thr - 1, (0, None))[0]
                if below > budget:
                    sstar = thr
                    break
        # fallback: smallest thr with maxI<=budget if no explosion-adjacent crossing found
        if sstar is None:
            for thr in range(k + 1, n + 1):
                if per_thr_maxI.get(thr, (0, None))[0] <= budget:
                    sstar = thr
                    break
        print(f"  p={p} (p/n^3={p/n**3:.1f}, m={m_index}):", flush=True)
        for thr in range(max(k + 1, n // 2 - 5), min(n, n // 2 + 4) + 1):
            mi, dd = per_thr_maxI.get(thr, (0, None))
            flag = "" if mi <= budget else " OVER"
            star = " <== binding s*" if thr == sstar else ""
            print(f"     s(thr)={thr:>3}  maxI={mi:>6}  worst_dir={dd}{flag}{star}", flush=True)
        ds = (n - sstar) / n if sstar else None
        print(f"   >>> s*={sstar}  delta*=(n-s*)/n={ds:.5f}  regimeA_pred_s*={n//2-1} "
              f"(Johnson={1-sqrt(rho):.4f})", flush=True)
    print(flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=16)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--mults', type=str, default="8,80")
    args = ap.parse_args()
    mults = [int(x) for x in args.mults.split(',')]
    run(args.n, args.k, mults)
