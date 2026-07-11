"""
probe_dsval_a4_genvander_fast.py  (ANGLE A4, fast)

Char-0 (complex roots of unity) worst-direction over-det delta*, vectorized over directions
per w-subset. Confirms n=8,16 and the closed form  delta* = 1 - rho - d/n  (d = critical
over-det depth = w_crit - k).  Reports the per-direction orbit structure at the threshold.

Mechanism = generalized-Vandermonde rank-deficiency:  x^a + gamma x^b agrees with a deg-<k poly
on a w-subset R  <=>  GV_R = [1,x,..,x^{k-1}, x^a, x^b]|_R has its two far columns reducible to
one (k+1)-codim constraint with common ratio gamma.  Computed by projecting both far columns off
the Vandermonde column space (QR) and checking residual collinearity.  This is exactly counting
vanishing Schur minors of GV at roots of unity = the #389/#400 dilation orbit count.
"""
import itertools, sys, cmath, math
import numpy as np

def gv_threshold(n, k, wmax_scan=None, dirs=None, budget=None, eps=1e-7):
    if budget is None: budget = n
    roots = np.array([cmath.exp(2j*math.pi*i/n) for i in range(n)])
    if dirs is None:
        dirs = list(itertools.combinations(range(k, n), 2))
    # precompute power columns
    P = {e: roots**e for e in set([c for c in range(k)] + [d for ab in dirs for d in ab])}
    # for each w from k+1 up: maxI over dirs; threshold = smallest w with maxI<=budget
    results = {}
    rng_w = range(k+1, n)
    for w in rng_w:
        subs = list(itertools.combinations(range(n), w))
        # precompute QR of Vandermonde per subset is the bottleneck; do it once per subset
        best = 0; bestdir = None; perdir = {}
        # Build Vandermonde stack: (Nsub, w, k)
        idx = np.array(subs)                              # (Nsub, w)
        Vand = np.stack([P[c][idx] for c in range(k)], axis=-1)  # (Nsub, w, k)
        # economy QR over batch
        Q, _ = np.linalg.qr(Vand)                        # Q: (Nsub, w, k) orthonormal cols
        for (a, b) in dirs:
            va = P[a][idx]; vb = P[b][idx]               # (Nsub, w)
            # residual after projecting off col space: r = v - Q (Q^H v)
            def resid(v):
                coef = np.einsum('swk,sw->sk', Q.conj(), v)
                return v - np.einsum('swk,sk->sw', Q, coef)
            ra = resid(va); rb = resid(vb)
            na = np.linalg.norm(ra, axis=1); nb = np.linalg.norm(rb, axis=1)
            gammas = set()
            for s in range(len(subs)):
                if nb[s] < eps:
                    if na[s] < eps:
                        gammas = None; break          # degenerate direction on this subset
                    continue
                if na[s] < eps:
                    gammas.add((0.0, 0.0)); continue
                lam = np.vdot(rb[s], ra[s]) / np.vdot(rb[s], rb[s])
                if np.linalg.norm(ra[s] - lam*rb[s]) < eps*max(na[s], 1.0):
                    g = -lam
                    gammas.add((round(g.real, 4), round(g.imag, 4)))
            if gammas is None:
                continue
            I = len(gammas)
            perdir[(a, b)] = I
            if I > best:
                best = I; bestdir = (a, b)
        results[w] = (best, bestdir)
        if best <= budget:
            return w, best, bestdir, results
    return None, None, None, results

if __name__ == "__main__":
    cases = [(8,2,0.25),(16,4,0.25),(8,4,0.5),(16,8,0.5)]
    measured = {(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    print("worst-direction char-0 over-det delta* + closed form  d* = 1-rho-d/n :",flush=True)
    for (n,k,rho) in cases:
        w,best,bd,res = gv_threshold(n,k)
        if w is None:
            print(f"  n={n} k={k}: no crossing",flush=True); continue
        ds = 1 - w/n; d = w - k
        m = measured[(n,k)]
        ok = 'MATCH' if abs(ds-m)<1e-9 else f'DIFFER({m})'
        print(f"  n={n} k={k} rho={rho}: w_crit={w} depth d={d} delta*={ds:.4f} [{ok}] "
              f"thresh I={best}@{bd}  | profile maxI(w)={[(ww,res[ww][0]) for ww in sorted(res)]}",flush=True)
    print("DONE",flush=True)
