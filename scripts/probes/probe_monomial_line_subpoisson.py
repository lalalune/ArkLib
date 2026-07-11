#!/usr/bin/env python3
"""
probe_monomial_line_subpoisson.py  (#407)

REFUTATION TEST for the Poisson-concentration conjecture (the NEW closed reframing of delta*):
  "The far-line incidence L(line) = #{gamma in F_q : u0 + gamma*u1 is delta-close to RS[k]} is
   SUB-POISSON over the n^2 MONOMIAL directions (X^a, X^b) -- i.e. max-line incidence ~ avg-line
   incidence -- so worst-case = average and delta* = 1 - rho - H(rho)/(beta log n) is pinned exactly."

If TRUE: for every radius, max over monomial lines of incidence ~ the average incidence (no heavy
line). If FALSE: some monomial line has incidence >> average (a KKH26-style heavy line) -> the
worst-case exceeds the budget -> the conjecture is refuted and delta* sits below the average-term.

PRIZE-SHAPED REGIME (per issue #407 sec 0): q = 12289 (prime FFT modulus), n = 8 = 2^3, so
mu_8 is a PROPER subgroup of F_q* (order 8 | 12288), beta = log_8 q ~ 4.5 (prize range), q ~ n^4.5 >> n^3.
NOT the full group (avoids the #400 artifact trap).

Per-line incidence is computed EXACTLY over all q scalars gamma (no enumeration of RS codewords):
a word v in F_q^n is delta-close to RS[k] iff some deg<k poly agrees with v on >= tau = n - floor(delta n)
coords.  We find the max agreement by interpolating through every k-subset of coords (any codeword
agreeing on >= tau > k coords is found from some k-subset of its agreement set) and taking the best.
Everything is vectorized over gamma via v_gamma = u0 + gamma*u1 (linear in gamma).
"""
import numpy as np
from itertools import combinations, product


def mu_subgroup(q, n):
    # generator of F_q^*
    def order(x):
        o, y = 1, x % q
        while y != 1:
            y = (y * x) % q; o += 1
        return o
    g = next(c for c in range(2, q) if order(c) == q - 1)
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, i, q) for i in range(n)})


def interp_eval_matrices(pts, q, k):
    """For each k-subset S of coords, the n×k 'evaluate the deg<k interpolant through S' linear map,
    as an n×n matrix M_S with v -> (interpolant through v|_S) evaluated at all n points.
    Returns list of (S, M_S) with M_S an (n,n) int matrix mod q acting on the full v (zero outside S)."""
    n = len(pts)
    pts = np.array(pts, dtype=np.int64)
    mats = []
    qq = q
    # Vandermonde rows for all points: V[i, j] = pts[i]^j, j=0..k-1
    Vfull = np.ones((n, k), dtype=np.int64)
    for j in range(1, k):
        Vfull[:, j] = (Vfull[:, j - 1] * pts) % qq
    for S in combinations(range(n), k):
        Vs = Vfull[list(S), :]                     # k×k Vandermonde on S
        Vs_inv = mat_inv_modp(Vs, qq)              # k×k inverse mod q
        if Vs_inv is None:
            continue                               # degenerate (shouldn't happen, distinct pts)
        # interpolant coeffs c = Vs_inv @ v|_S ; values at all pts = Vfull @ c = (Vfull @ Vs_inv) @ v|_S
        Meval = (Vfull @ Vs_inv) % qq              # n×k : maps v|_S (k-vec) to n values
        mats.append((list(S), Meval))
    return mats


def mat_inv_modp(A, p):
    n = A.shape[0]
    M = np.concatenate([A % p, np.eye(n, dtype=np.int64)], axis=1) % p
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r, col] % p != 0:
                piv = r; break
        if piv is None:
            return None
        M[[col, piv]] = M[[piv, col]]
        inv = pow(int(M[col, col]), p - 2, p)
        M[col] = (M[col] * inv) % p
        for r in range(n):
            if r != col and M[r, col] % p != 0:
                M[r] = (M[r] - M[r, col] * M[col]) % p
    return M[:, n:] % p


def line_incidence_profile(u0, u1, mats, q, n, k, gammas, taus):
    """For line v_gamma = u0 + gamma u1, return dict tau -> #{gamma : v_gamma delta-close (agree>=tau)}."""
    G = gammas.shape[0]
    # v_gamma over all gamma: shape (G, n) = u0[None,:] + gamma[:,None]*u1[None,:]
    V = (u0[None, :] + np.outer(gammas, u1)) % q       # (G, n)
    best = np.zeros(G, dtype=np.int64)                 # best agreement count per gamma
    for S, Meval in mats:
        vS = V[:, S]                                   # (G, k)
        pred = (vS @ Meval.T) % q                      # (G, n) interpolant values at all n pts
        agree = np.sum(pred == V, axis=1)              # (G,) agreement count
        np.maximum(best, agree, out=best)
    return {tau: int(np.sum(best >= tau)) for tau in taus}


def run(q, n, k, rho_label):
    pts = mu_subgroup(q, n)
    ptsv = np.array(pts, dtype=np.int64)
    mats = interp_eval_matrices(pts, q, k)
    gammas = np.arange(q, dtype=np.int64)
    taus = list(range(k + 1, n + 1))                   # agreement thresholds > k (beyond unique interp)
    # monomial directions: u_a = (y^a)_{y in mu_n}, exponents a in 0..n-1 (y^n=1)
    powmat = np.ones((n, n), dtype=np.int64)           # powmat[a] = (y^a)
    for a in range(1, n):
        powmat[a] = (powmat[a - 1] * ptsv) % q
    print(f"\n=== q={q} n={n} k={k} ({rho_label}); proper subgroup mu_{n}, beta=log_{n}q≈{np.log(q)/np.log(n):.2f} ===")
    print(f"   taus (agreement thresholds) = {taus}  (delta = (n-tau)/n)")
    # collect incidence over all monomial lines (a,b), a!=b, excluding subgroup dir b s.t. y^b=±1 trivially
    from math import gcd
    # PRIMITIVE far lines: gcd(a,n)=gcd(b,n)=1 (X^a, X^b generate the full mu_n, no tower collapse).
    # IMPRIMITIVE: at least one exponent shares a factor with n (maps mu_n -> proper sub-subgroup).
    exps = [e for e in range(k, n) if e != n // 2]
    prim = {tau: [] for tau in taus}
    imprim = {tau: [] for tau in taus}
    imheavy = {tau: (0, None) for tau in taus}
    primheavy = {tau: (0, None) for tau in taus}
    for a, b in product(exps, repeat=2):
        if a == b:
            continue
        prof = line_incidence_profile(powmat[a], powmat[b], mats, q, n, k, gammas, taus)
        is_prim = (gcd(a, n) == 1 and gcd(b, n) == 1)
        for tau in taus:
            (prim if is_prim else imprim)[tau].append(prof[tau])
            tgt = primheavy if is_prim else imheavy
            if prof[tau] > tgt[tau][0]:
                tgt[tau] = (prof[tau], (a, b))
    print(f"   {'tau':>4} {'delta':>7} | {'PRIM avg':>9} {'PRIM max':>9} {'p_m/a':>6} {'argmax':>8} || "
          f"{'IMPRIM avg':>10} {'IMPRIM max':>10} {'i_m/a':>7} {'argmax':>8}")
    for tau in taus:
        pa = np.array(prim[tau], dtype=float); ia = np.array(imprim[tau], dtype=float)
        pav = pa.mean() if len(pa) else 0; pmx = pa.max() if len(pa) else 0
        iav = ia.mean() if len(ia) else 0; imx = ia.max() if len(ia) else 0
        pr = pmx / pav if pav > 0 else float('nan')
        ir = imx / iav if iav > 0 else float('nan')
        delta = (n - tau) / n
        print(f"   {tau:>4} {delta:>7.3f} | {pav:>9.2f} {pmx:>9.0f} {pr:>6.2f} {str(primheavy[tau][1]):>8} || "
              f"{iav:>10.2f} {imx:>10.0f} {ir:>7.2f} {str(imheavy[tau][1]):>8}")
    print(f"   exps={exps}; primitive(gcd=1)={[e for e in exps if gcd(e,n)==1]}, "
          f"imprimitive={[e for e in exps if gcd(e,n)>1]}")
    print("   [PRIMITIVE max/avg ~ O(1) => sub-Poisson on the genuine generic family; "
          "IMPRIMITIVE = the 2-power-tower heavy lines = open core]")


if __name__ == "__main__":
    q = 12289   # 12288 = 2^12 * 3, so 8|.. and 16|.. ; proper subgroups for n in {8,16}
    run(q, 8, 4, "rho=1/2")
    run(q, 8, 2, "rho=1/4")
    run(q, 8, 1, "rho=1/8")
    # n=16 confirmation (small k so C(16,k) subsets stay cheap)
    run(q, 16, 2, "rho=1/8")
    run(q, 16, 3, "rho~3/16")
