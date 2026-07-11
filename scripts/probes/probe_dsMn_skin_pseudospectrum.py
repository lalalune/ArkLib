#!/usr/bin/env python3
"""
probe_dsMn_skin_pseudospectrum.py  (NOT committed; scratch probe)

EXOTIC DOMAIN: non-Hermitian / skin-effect / transfer-operator attack on
    M(n) = max_{b!=0} |sum_{x in mu_n} e_p(b x)|,   mu_n = 2-power subgroup of F_p.

The in-tree dilation recursion is f_{i+1}(b) = f_i(b) + f_i(zeta*b)  (eta_union_dilate).
Lane A1 (_wf5A1_phase_transfer_spectral.lean) already refuted the WORST-FREQUENCY
scalar telescope: per-level worst ratio geomean ~ 1.5 > sqrt(2), because the
maximizer b* MIGRATES between levels.

The genuinely NEW non-Hermitian question (skin-effect lens):
  The level map is a LINEAR operator T on the full m-vector (f over a tower coset orbit),
  T = I + (shift by zeta) acting on the orbit b -> zeta*b -> zeta^2*b -> ...
  This is a NON-RECIPROCAL (one-directional) circulant-like operator = the canonical
  skin-effect Hatano-Nelson object. Non-normal operators have:
     spectral_radius(T) <= ||T|| , often STRICT (the gap = non-normality).
  Iterated bound M(2^L) is governed by ||T^L||, which for non-normal T can:
     (a) be controlled by spectral_radius if T were diagonalizable with bounded cond,
     (b) but for SKIN operators the eigenvector condition number GROWS exponentially
         (this is the skin effect), so ||T^L|| ~ rho^L only after a transient that
         itself grows -> the spectral radius does NOT control the finite-L norm.

So the test: compute, for the actual orbit transfer operator at each level,
  - the operator 2-norm ||T|| (governs single step, expect ~ alignment),
  - the spectral radius rho(T) (governs asymptotic iterate),
  - the eigenvector condition number kappa(V) (skin = blows up),
  - and CRUCIALLY ||T^L|| / 2^{L/2}  (does the iterate beat the flat sqrt-law?).

If rho(T) < sqrt(2) BUT kappa(V) blows up so ||T^L|| still >= sqrt(2)^L, the skin
refinement REPRODUCES the no-go (collapses to BGK). If ||T^L|| genuinely < sqrt(2)^L
for the RS-restricted sector, that's a real handle.
"""
import numpy as np

def find_prime_with_subgroup(mu_exp, beta=2.0, search=2000):
    """find prime p with 2^mu | p-1, p ~ n^beta."""
    n = 2**mu_exp
    target = int(n**beta)
    p = target | 1
    for _ in range(search*50):
        if (p-1) % n == 0 and is_prime(p):
            return p, n
        p += 2
    return None, n

def is_prime(m):
    if m < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def primitive_root(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
    return None

def eta(p, gens, b):
    # sum over x in subgroup gens of e_p(b*x)  (vectorized)
    g = np.asarray(gens, dtype=np.int64)
    return np.exp(2j*np.pi*((b*g) % p)/p).sum()

def all_eta(p, gens):
    # |eta_b| for all b in 1..p-1 at once: rows=b, cols=x ; O(p*n) but numpy-fast
    g = np.asarray(gens, dtype=np.int64)
    b = np.arange(1, p, dtype=np.int64)
    ph = np.exp(2j*np.pi*((np.outer(b, g)) % p)/p).sum(axis=1)
    return np.abs(ph)

def subgroup(p, g, n):
    h = pow(g,(p-1)//n,p)
    out=[1]; cur=1
    for _ in range(n-1):
        cur=cur*h%p; out.append(cur)
    return out

def analyze(mu_exp, beta):
    p,n = find_prime_with_subgroup(mu_exp, beta)
    if p is None:
        print(f"  mu={mu_exp}: no prime found"); return
    g = primitive_root(p)
    # zeta of order 2n: generator h2 = g^((p-1)/(2n)); zeta acts b->zeta*b
    # We build the level-(mu) operator T on the orbit of the worst frequency under b->zeta*b.
    # Orbit length under mult by zeta (order 2n) is 2n. The transfer on the eta-vector
    # indexed by orbit position: (T f)(j) = f(j) + f(j+1)  with shift by zeta  -> bidiagonal
    # NON-RECIPROCAL one-way coupling = Hatano-Nelson skin operator (circulant with wrap).
    zeta = pow(g,(p-1)//(2*n),p)  # order 2n
    sub_n = subgroup(p,g,n)
    # worst frequency at level n
    Ms = all_eta(p, sub_n)
    bstar = int(np.argmax(Ms))+1
    Mn = float(np.max(Ms))
    # orbit of bstar under mult by zeta (length divides 2n)
    orbit=[bstar]; cur=bstar
    while True:
        cur=cur*zeta%p
        if cur==bstar: break
        orbit.append(cur)
    L=len(orbit)
    # The non-reciprocal skin transfer operator: T = I + P, P = one-way shift on orbit
    # (the +zeta*b term moves you one step along the orbit). With periodic wrap = skin ring.
    P = np.zeros((L,L),dtype=complex)
    for j in range(L):
        P[j,(j+1)%L]=1.0
    T = np.eye(L)+P
    # operator 2-norm, spectral radius, eigenvector condition number
    svals = np.linalg.svd(T, compute_uv=False)
    opnorm = svals[0]
    w,V = np.linalg.eig(T)
    rho = max(abs(w))
    try: kappa = np.linalg.cond(V)
    except Exception: kappa = float('inf')
    # iterate norm ||T^L||  vs sqrt(2)^L  (does non-normal iterate beat flat law?)
    # use L_steps = number of dyadic levels from n to ~ p (i.e. log2 of orbit), but
    # the meaningful telescope length is mu (levels in the 2^mu tower). Use steps=mu_exp.
    steps = mu_exp
    TL = np.linalg.matrix_power(T, steps)
    iter_norm = np.linalg.norm(TL,2)
    flat = (2**0.5)**steps
    print(f"  mu={mu_exp} p={p} n={n} bstar={bstar} M(n)={Mn:.3f}  orbitlen={L}")
    print(f"     ||T||={opnorm:.4f}  rho(T)={rho:.4f}  kappa(V)={kappa:.3e}")
    print(f"     ||T^{steps}||={iter_norm:.4f}  sqrt2^{steps}={flat:.4f}  ratio={iter_norm/flat:.4f}")
    print(f"     M(n)/sqrt(2 n ln p)={Mn/np.sqrt(2*n*np.log(p)):.4f}")
    return rho, opnorm, iter_norm/flat

if __name__=="__main__":
    print("=== non-Hermitian skin / transfer-operator probe on M(n) ===")
    print("T = I + one-way-shift (Hatano-Nelson skin ring on the zeta-orbit)")
    for mu in [4,5,6,7,8]:
        analyze(mu, beta=2.0)
