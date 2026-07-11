"""
probe_dsval_a4_genvander_vec.py  (ANGLE A4, fully vectorized collinearity)

Confirm n=16 worst-direction over-det delta* by computing maxI(w) at the crossing only.
Fully vectorizes the residual-collinearity test across ALL subsets (no per-subset Python loop).
Char-0 via complex roots of unity. Reports the orbit structure (#distinct gamma) at each w.
"""
import itertools, cmath, math
import numpy as np

def maxI(n, k, w, dirs, eps=1e-7):
    roots = np.array([cmath.exp(2j*math.pi*i/n) for i in range(n)])
    subs = np.array(list(itertools.combinations(range(n), w)))      # (N,w)
    N = len(subs)
    Vand = np.stack([(roots**c)[subs] for c in range(k)], axis=-1)  # (N,w,k)
    Q, _ = np.linalg.qr(Vand)                                        # (N,w,k)
    out = {}
    for (a, b) in dirs:
        va = (roots**a)[subs]; vb = (roots**b)[subs]                 # (N,w)
        ca = np.einsum('swk,sw->sk', Q.conj(), va)
        cb = np.einsum('swk,sw->sk', Q.conj(), vb)
        ra = va - np.einsum('swk,sk->sw', Q, ca)
        rb = vb - np.einsum('swk,sk->sw', Q, cb)
        na = np.linalg.norm(ra, axis=1); nb = np.linalg.norm(rb, axis=1)
        # lam = <rb,ra>/<rb,rb>, gamma = -lam, valid where rb collinear with ra
        rbn2 = np.einsum('sw,sw->s', rb.conj(), rb).real
        dot  = np.einsum('sw,sw->s', rb.conj(), ra)
        lam = np.where(rbn2 > eps*eps, dot/np.maximum(rbn2, 1e-30), 0.0)
        coll = np.linalg.norm(ra - lam[:,None]*rb, axis=1)
        # bad subset: nb>eps (b far col not in code) AND residuals collinear
        bad = (nb > eps) & (coll < eps*np.maximum(na, 1.0))
        # also na<eps with nb<eps -> degenerate; skip that direction if any fully-degenerate subset
        degen = (nb <= eps) & (na <= eps)
        if degen.any():
            out[(a, b)] = None
            continue
        g = -lam[bad]
        gammas = set(zip(np.round(g.real, 4), np.round(g.imag, 4)))
        out[(a, b)] = len(gammas)
    vals = {d: v for d, v in out.items() if v is not None}
    best = max(vals.values()) if vals else 0
    bestdir = max(vals, key=lambda d: vals[d]) if vals else None
    return best, bestdir, vals

if __name__ == "__main__":
    import sys
    # n=16 rho=1/4: k=4, expect w_crit=7 (delta*=0.5625). Check w=6 (>n) and w=7 (<=n).
    for (n, k, label, wrange) in [(16,4,"rho=1/4",[5,6,7,8]), (16,8,"rho=1/2",[9,10,11,12])]:
        dirs = list(itertools.combinations(range(k, n), 2))
        print(f"n={n} k={k} {label} budget={n}:", flush=True)
        cross = None
        for w in wrange:
            best, bd, vals = maxI(n, k, w, dirs)
            tag = "ok<=n" if best <= n else "OVER"
            print(f"   w={w} delta={1-w/n:.4f}: maxI={best} @ {bd}  [{tag}]", flush=True)
            if best <= n and cross is None:
                cross = (w, best, bd)
        if cross:
            w, best, bd = cross
            print(f"   => delta* = {1-w/n:.4f}  depth d = {w-k}  thresh I={best}@{bd}", flush=True)
    print("DONE", flush=True)

# ============================================================================
# RESULT (2026-06-14, ANGLE A4 generalized-Vandermonde / higher-order-MDS, char 0)
# ----------------------------------------------------------------------------
# All 4 orchestrator-measured worst-direction delta* REPRODUCED via GV rank-deficiency:
#   (n,rho)   k   d=2 row maxI         d=3 row maxI        delta*    depth d   thresh dir / orbit
#   (8 ,1/4)  2   w=4: 9   [OVER 8]    w=5: 8  [ok]        0.3750    3         (4,5) I=8  =1 full orbit S=8, |g|=1
#   (16,1/4)  4   w=6: 89  [OVER 16]   w=7: 9  [ok]        0.5625    3         (8,14) I=9 =1 orbit S=8 + gamma0
#   (8 ,1/2)  4   w=5 ...               w=6: 8  [ok]        0.2500    2         (4,5)-type single orbit
#   (16,1/2)  8   w=10:40  [OVER 16]   w=11: 4 [ok]        0.3125    3         (8,12) I=4 =1 full orbit S=4, |g|=1
#
# CLOSED FORM (exact, q-independent, verified on all 4 points):
#     delta*(n,rho) = 1 - rho - d(n,rho)/n,    d = w_crit - k = critical over-det DEPTH
#     where d = min{ depth : max_dir I(k+depth) <= budget n }.
# Measured d = {3, 3, 2, 3}.  delta* = (1-rho) - d/n.
#
# RANK CLIFF: maxI(w) drops super-fast across the critical depth (3984 -> 89 -> 9;
#   10288 -> 40 -> 4): the generalized Vandermonde M=[V_k | x^a | x^b] becomes
#   higher-order-MDS (Schur minors generically nonvanishing) at a sharp depth; the small
#   surviving residual = configs where a cyclotomic Schur minor still vanishes.
#
# THRESHOLD VALUE = EXACTLY ONE DILATION ORBIT (size S=n/gcd(b-a,n)), +0/1 from gamma=0.
#   => ANGLE A4 REDUCES TO THE SAME #389/#400 DILATION-ORBIT COUNT.  The char-0 NVM
#   (Lovett / GM-MDS, in-tree HigherOrderMDS.IsGenericInter) gives only the GENERIC zero;
#   the EXACT residual count is the cyclotomic Schur-vanishing = the open orbit count.
#
# OPEN: whether d(n,rho) -> const (=> delta* -> 1-rho = CAPACITY, breakthrough) or grows
#   like Theta(n/log n) (=> delta* = 1-rho-Theta(1/log n), window edge).  Only n=8,16 are
#   brute-force-reachable; d=3 at both n=16 rows is consistent with EITHER.  NOT pinnable
#   from available exact data.  This is the genuine open residual.
# ============================================================================
