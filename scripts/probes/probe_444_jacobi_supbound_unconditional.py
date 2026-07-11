#!/usr/bin/env python3
"""
probe_444_jacobi_supbound_unconditional.py  (sol, door-(iv) Lane-2, 2026-06-21)

GOAL: nail down which facts of Shaw's NEW Jacobi/recurrence-coefficient tool
(deltastar-444-JACOBI-RECURRENCE-TOOL-2026-06-21.md) are UNCONDITIONALLY,
ARITHMETIC-FREE provable (-> candidates for axiom-clean Lean Lane-2 hardening),
vs which need the (conjectural) sub-Gaussian fine structure (= the wall).

For a finitely supported real measure mu = sum_x w_x delta_x (w_x>0, sum=1):
  - Jacobi matrix J (tridiagonal, diag a_k, offdiag b_k>0) from 3-term recurrence
    of the orthonormal polynomials of mu.
  - CLASSICAL FACTS (Stieltjes/Stone; we VERIFY them empirically here so the Lean
    statement is honest about what is being relied on):
      (F1)  max support point  S := max_x x  equals  topeig(J_R) as R -> #supp.
      (F2)  every recurrence coeff  |a_k| <= S_abs := max_x |x|   and  b_k <= S_abs.
            (Jacobi matrix entries are bounded by the support radius — this is the
             ONLY arithmetic-free upper bound; gives the trivial M <= n ceiling.)
      (F3)  topeig(J_R) <= ||J_R||_op <= max_k(|a_k| + b_k + b_{k-1}) <= 3*S_abs
            (Gershgorin) — a clean *operator-norm* upper bound on M via the b_k.
  - We test on the REAL Paley/eta object (eta_b over thin mu_n) so the support is
    the actual {Re eta_b} (or |eta_b|), NOT a toy.

We are looking for the UNCONDITIONAL b_k-> M upper bound (Lane-2 honest ceiling),
NOT the conjectural (1/sqrt2)sqrt(n log p) (that's the wall, stays a probe note).
"""
import numpy as np, cmath, math, sys

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, beta):
    # p prime, n | p-1, p ~ n^beta, p >> n^3 (prize regime)
    target = int(n**beta)
    p = target - (target % n) + 1
    for _ in range(200000):
        if p > n**3 and is_prime(p):
            return p
        p += n
    return None

def subgroup(n, p):
    # mu_n = unique order-n subgroup of F_p^*
    g = None
    for cand in range(2, p):
        # check generator-ish: cand^((p-1)/n) has order n
        h = pow(cand, (p-1)//n, p)
        if pow(h, n, p) == 1 and all(pow(h, n//f, p) != 1 for f in set(prime_factors(n))):
            g = h; break
    if g is None:
        # fallback: any element of order dividing n; build via a known generator
        for cand in range(2, p):
            if pow(cand, (p-1)//n, p) != 1 or True:
                h = pow(cand, (p-1)//n, p)
                S = set(pow(h, j, p) for j in range(n))
                if len(S) == n:
                    g = h; break
    return [pow(g, j, p) for j in range(n)]

def prime_factors(m):
    f = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            f.add(d); m//=d
        d += 1
    if m>1: f.add(m)
    return f

def eta_values(n, p):
    """eta_b = sum_{x in mu_n} e_p(b x), for b=1..p-1. Vectorized over b.
    Return real parts (a real measure for the Jacobi recurrence) and |eta_b|."""
    grp = np.array(subgroup(n, p), dtype=np.int64)
    b = np.arange(1, p, dtype=np.int64)
    # phases[b,x] = (b*grp[x]) mod p ; sum over x of exp(2pi i phase/p)
    w = 2*math.pi/p
    re = np.zeros(p-1); im = np.zeros(p-1)
    # chunk over b to bound memory
    CH = 200000
    for i in range(0, len(b), CH):
        bb = b[i:i+CH][:,None]                 # (m,1)
        ph = (bb * grp[None,:]) % p            # (m,n)
        ang = w*ph
        re[i:i+CH] = np.cos(ang).sum(axis=1)
        im[i:i+CH] = np.sin(ang).sum(axis=1)
    ab = np.sqrt(re*re+im*im)
    return re, ab

def jacobi_from_measure(support, weights, R):
    """Stieltjes: orthonormal polynomial recurrence -> (a_k, b_k), k=0..R-1.
    weights sum to 1, weights>0. Returns a[0..R-1], b[1..R-1]."""
    x = np.asarray(support, float)
    w = np.asarray(weights, float)
    w = w / w.sum()
    N = len(x)
    R = min(R, N)
    a = np.zeros(R); b = np.zeros(R)
    # p_{-1}=0, p_0=1 (monic); use modified Chebyshev / direct Stieltjes
    pkm1 = np.zeros(N)         # p_{-1}
    pk = np.ones(N)            # p_0 (monic)
    norm_k = (w*pk*pk).sum()   # <p_0,p_0>
    for k in range(R):
        a[k] = (w*x*pk*pk).sum()/norm_k
        if k == 0:
            pkp1 = (x - a[k])*pk
        else:
            pkp1 = (x - a[k])*pk - b[k]*pkm1   # b[k]=beta_k (squared offdiag, monic conv)
        norm_kp1 = (w*pkp1*pkp1).sum()
        if k+1 < R:
            b[k+1] = norm_kp1/norm_k   # monic beta_{k+1} = ||p_{k+1}||^2/||p_k||^2
        pkm1, pk = pk, pkp1
        norm_k = norm_kp1
        if norm_k <= 0: 
            R = k+1; a=a[:R]; b=b[:R]; break
    # orthonormal offdiag = sqrt(beta_k)
    boff = np.sqrt(np.maximum(b[1:R], 0.0))
    return a[:R], boff   # a_k diag (R), b_k offdiag (R-1)

def topeig_jacobi(a, boff):
    R = len(a)
    J = np.zeros((R,R))
    for k in range(R): J[k,k]=a[k]
    for k in range(len(boff)):
        J[k,k+1]=boff[k]; J[k+1,k]=boff[k]
    ev = np.linalg.eigvalsh(J)
    return ev.max(), J

def run(n, beta=4.0):
    p = find_prime(n, beta)
    if p is None:
        print(f"n={n}: no prime"); return
    re, ab = eta_values(n, p)
    M = ab.max()                       # the real target: max_b |eta_b|
    Sabs_re = np.abs(re).max()         # support radius of the REAL measure (Re eta)
    Smax_re = re.max()
    # empirical measure of Re(eta_b)
    support = re
    weights = np.ones_like(support)/len(support)
    R = max(4, int(2*math.log(p))+2)
    a, boff = jacobi_from_measure(support, weights, R)
    teig, J = topeig_jacobi(a, boff)
    maxb = boff.max() if len(boff) else 0.0
    maxa = np.abs(a).max()
    gersh = (np.abs(a) + np.r_[boff,0] + np.r_[0,boff]).max()
    print(f"n={n:4d} p={p:>10d} logp={math.log(p):5.2f}  M(|eta|)={M:8.3f}  "
          f"max Re eta={Smax_re:8.3f}  topeig(J)={teig:8.3f}")
    print(f"        support_radius |x|max={Sabs_re:7.3f}  max_k|a_k|={maxa:7.3f}  "
          f"max_k b_k={maxb:7.3f}  (b<=radius? {maxb<=Sabs_re+1e-9})  "
          f"(|a|<=radius? {maxa<=Sabs_re+1e-9})")
    print(f"        topeig<=max Re eta? {teig<=Smax_re+1e-6}  "
          f"Gershgorin ||J||<=3*radius? {gersh<=3*Sabs_re+1e-6}  "
          f"(Gershgorin bound={gersh:.3f}, 3*radius={3*Sabs_re:.3f})")
    print(f"        ratio topeig/maxReEta={teig/Smax_re:.4f}  2*maxb/M={2*maxb/M:.4f}  "
          f"radius/n={Sabs_re/n:.4f}")
    return dict(n=n,p=p,M=M,teig=teig,Smax_re=Smax_re,Sabs_re=Sabs_re,maxb=maxb,maxa=maxa,gersh=gersh)

if __name__ == "__main__":
    print("=== Jacobi tool: UNCONDITIONAL (arithmetic-free) facts probe ===")
    print("F1: topeig(J) = max support point of empirical measure")
    print("F2: |a_k|<=radius, b_k<=radius  (Jacobi entries bounded by support radius)")
    print("F3: topeig <= Gershgorin op-norm <= 3*radius")
    print()
    import os
    ns = [int(x) for x in os.environ.get('NS','8,16,32').split(',')]
    for n in ns:
        try: run(n)
        except Exception as e: print(f"n={n}: ERR {e}")
        print()
