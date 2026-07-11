#!/usr/bin/env python3
"""
A6 diagnostic-3 — Is the Schur-Siegel-Smyth trace-problem machinery even
APPLICABLE to the Gaussian periods, and if so does it give max|eta|<=C sqrt(n)?

SSS trace problem (precise): for a TOTALLY POSITIVE algebraic integer alpha of
degree d with conjugates alpha=alpha_1,...,alpha_d > 0, the absolute trace
(1/d) sum alpha_i >= c for an absolute constant c > 1.78... (Smyth). This is a
LOWER bound on the MEAN of the conjugates, derived from auxiliary-polynomial /
LP duality on the integer power sums (resultant positivity).

To bound max|eta_i| from ABOVE via SSS-style ideas we would need an UPPER bound
on a trace, which SSS does NOT directly give. The honest test:

  (i) Galois structure: is Psi_p irreducible over Q (the m periods = one orbit)?
      If reducible, the "period algebraic integer" has smaller degree and the
      power-sum constraints are over that orbit.
  (ii) Build the SHIFTED totally-positive integer that SSS could grip:
       beta_i = M_target^2 - eta_i^2  (>=0 iff |eta_i|<=M_target). The eta_i^2 are
       algebraic integers (Galois-stable multiset). If beta = c - eta^2 is totally
       positive for c = upper bound we want to PROVE, SSS gives a LOWER bound on
       its mean trace -- i.e. SSS can CERTIFY (1/d)sum(c-eta_i^2)>=1.78, an averaged
       statement = the Parseval second moment again, NOT a max bound.
  (iii) The decisive structural check: the trace problem is an AVERAGE statement.
       max|eta| is an L^infinity statement. The ONLY way SSS-type LP duality bounds
       an L-infinity max is via the integer power-sum SEQUENCE P_1,P_2,...,P_K with
       K -> infinity (the auxiliary polynomial sees all of them). For ANY finite K,
       the LP is loose by the sqrt(p) gap shown in diagnostic-2. As K->m we just
       reconstruct the polynomial = the domain. Quantify: solve the LP
         maximize t  s.t.  exists prob measure mu on R with
            integral x^k dmu = P_k/m for k=1..K, and t = max support point.
       (moment problem; the K-truncated max is the largest root of the orthogonal
       polynomial / Hankel boundary). Show this truncated-LP max stays ~sqrt(p),
       far above sqrt(n), for all small K -- i.e. SSS-truncations don't bind.
"""
import math, cmath
from sympy import isprime, Poly, symbols, ZZ, factor_list
import numpy as np

def primitive_root(p):
    phi=p-1; fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def periods_real(p,n):
    m=(p-1)//n; g=primitive_root(p)
    gm=pow(g,m,p); sub=[]; cur=1
    for _ in range(n): sub.append(cur); cur=cur*gm%p
    tp=2*math.pi/p
    def ps(b): return sum(cmath.exp(1j*tp*((b*x)%p)) for x in sub)
    re=[]; gi=1
    for i in range(m): re.append(ps(gi).real); gi=gi*g%p
    return re,m

def hankel_truncated_max(Pk_over_m, K):
    """
    Truncated moment-problem max-support: given moments mu_k = P_k/m for k=0..K
    (mu_0=1), the largest possible support point of a measure with these moments
    is the largest root of the degree-(K//2 +1) determinant condition; a clean
    computable proxy is the largest root of the (K)-truncated orthogonal-polynomial
    recurrence, OR simply the largest generalized eigenvalue of the Hankel pencil
    (H1, H0) where H0 = [mu_{i+j}], H1 = [mu_{i+j+1}], i,j=0..t, t=K//2.
    Largest gen-eigenvalue ~ truncated upper edge of support.
    """
    t = K//2
    H0 = np.array([[Pk_over_m[i+j] for j in range(t+1)] for i in range(t+1)])
    H1 = np.array([[Pk_over_m[i+j+1] for j in range(t+1)] for i in range(t+1)])
    # generalized eigenvalues of H1 x = lam H0 x ; largest = upper support edge
    try:
        from scipy.linalg import eig
        w = eig(H1, H0, right=False)
        w = np.real(w[np.abs(np.imag(w))<1e-6])
        return float(np.max(w))
    except Exception:
        # fallback: solve H0^{-1} H1
        w = np.linalg.eigvals(np.linalg.solve(H0,H1))
        w = np.real(w[np.abs(np.imag(w))<1e-6])
        return float(np.max(w))

def run(p,n,Kmax=8):
    re,m=periods_real(p,n)
    M=max(abs(x) for x in re)
    moms=[1.0]+[ (sum(x**k for x in re)/m) for k in range(1,Kmax+1)]
    sqrtn=math.sqrt(n); sqrtp=math.sqrt(p)
    print(f"p={p} n={n} m={m}: M={M:.3f} M/sqrtn={M/sqrtn:.3f} sqrtp={sqrtp:.1f}")
    print(f"   moments mu_k=P_k/m: " + ", ".join(f"{moms[k]:.3g}" for k in range(0,Kmax+1)))
    for K in [2,4,6,8]:
        if K>Kmax: break
        try:
            hm=hankel_truncated_max(moms,K)
            print(f"   K={K}: truncated moment-problem max support = {hm:.2f}"
                  f"   (max/sqrtn={hm/sqrtn:.2f}, max/M={hm/M:.2f})")
        except Exception as e:
            print(f"   K={K}: hankel failed {e}")

def find_primes(n,count,pmin):
    out=[]; t=pmin//n+1
    while len(out)<count:
        p=1+n*t
        if isprime(p): out.append(p)
        t+=1
    return out

if __name__=="__main__":
    print("=== A6 SSS applicability / truncated moment-problem upper edge ===")
    print("If truncated max stays >> sqrt(n) for all small K, SSS-truncations are")
    print("loose: the bound to sqrt(n) needs ALL moments (= the domain).\n")
    for mu in [3,4,5]:
        n=2**mu; pmin=max(50*n**3,1000)
        for p in find_primes(n,2,pmin):
            run(p,n); print()
