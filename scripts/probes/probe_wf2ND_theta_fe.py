#!/usr/bin/env python3
"""
wf-ND lane (#407): Approximate functional equation / theta-transformation for the SUBGROUP
Gauss sum  eta_b = sum_{x in mu_n} e_p(b x),  mu_n = degree-n mult subgroup of F_p^*.

NEW LENS (untouched in-tree): the classical QUADRATIC incomplete Gauss sum sum_{x<=N} e_p(x^2)
has a van der Corput / Hardy-Littlewood approximate FUNCTIONAL EQUATION; Demirci-Akarsu-Marklof
(arXiv:1207.1607) give its limiting value distribution (a self-similar theta law on the metaplectic
horocycle, heavy tail ~ R^-4, cusp excursions of size m^{1/4}). The in-tree dyadic work is about
MAGNITUDES (the false descent M^2<=2M(n/2)^2) or the ADDITIVE FFT butterfly (geometric phase; the
in-tree honest caveat already notes the theta machinery does NOT directly apply). This probe asks
the phase-aware question that decides the theta route:

  Does {eta_b/sqrt(n)} follow the Demirci-Akarsu-Marklof SELF-SIMILAR theta law (=> a contractive
  renormalization to exploit), or i.i.d. complex GAUSSIAN (=> NO self-similar law => theta route
  gives no contraction)?

VERDICT (exact, n=8..64, multi-prime incl. thin beta~5): i.i.d. complex GAUSSIAN. The theta route
is PINNED (no contraction). See docs/kb/deltastar-407-wf2ND-theta-fe-pin.md.
"""
import sympy, math
import numpy as np

def all_periods(p, n, include_zero=False):
    g = int(sympy.primitive_root(p))
    zeta = pow(g, (p-1)//n, p)
    mu = np.array([pow(zeta, j, p) for j in range(n)], dtype=np.int64)
    b = np.arange(0 if include_zero else 1, p, dtype=np.int64)
    ph = np.outer(mu, b) % p
    return np.exp(2j*math.pi*ph/p).sum(axis=0)

def test_A(p, n):
    z = all_periods(p, n) / math.sqrt(n)
    az = np.abs(z)
    m2, m4, m6 = np.mean(az**2), np.mean(az**4), np.mean(az**6)
    re = z.real
    return dict(rk_complex=float(m4/m2**2),     # complex Gaussian -> 2.0 ; DAM heavy tail -> >>2
                rk6=float(m6/m2**3),            # complex Gaussian -> 6.0
                re_kurt=float(np.mean(re**4)/np.mean(re**2)**2),  # real Gaussian -> 3.0
                maxz=float(np.max(az)),
                tail={R: round(float(np.mean(az>R)),6) for R in (2.0,2.5,3.0,3.5)})

def test_tail(p, n):
    az = np.abs(all_periods(p,n))/math.sqrt(n)
    return {R: (round(float(np.mean(az>R)),7), round(math.exp(-R*R),7), round(R**-4,5))
            for R in (1.5,2.0,2.5,3.0,3.5,4.0)}   # (empirical, Rayleigh e^-R^2, DAM R^-4)

def test_B(p, n):
    g = int(sympy.primitive_root(p)); sup = {}
    for nn in (n, n//2, n//4, n//8):
        if nn < 2: continue
        sup[nn] = float(np.max(np.abs(all_periods(p, nn))))
    lv = sorted(sup.keys(), reverse=True)
    ratios = {f"sup({lv[i]})/sup({lv[i+1]})": round(sup[lv[i]]/sup[lv[i+1]],4) for i in range(len(lv)-1)}
    ratios["sqrt2"] = round(math.sqrt(2),4)
    ratios["sup/sqrt(n)"] = {k: round(v/math.sqrt(k),3) for k,v in sup.items()}
    return ratios

def test_C(p, n):
    """Poisson/theta self-duality: DFT(1_{mu_n}) = eta; DFT(eta) recovers reflected 1_{mu_n}.
    Support of the dual = n (NO shortening => fixed point, not a contraction)."""
    g=int(sympy.primitive_root(p)); zeta=pow(g,(p-1)//n,p)
    mu=set(pow(zeta,j,p) for j in range(n))
    eta=np.array([sum(np.exp(2j*math.pi*((b*x)%p)/p) for x in mu) for b in range(p)])
    supp=set()
    for x in range(p):
        v=np.sum(eta*np.exp(-2j*math.pi*(np.arange(p)*x)/p))/p
        if abs(v)>0.5: supp.add(x)
    return dict(dual_support_size=len(supp), target_n=n, equals_mu_n=(supp==mu),
                parseval_relerr=abs(np.sum(np.abs(eta)**2)-p*n)/(p*n))

if __name__ == "__main__":
    print("="*74)
    print("TEST A -- value distribution eta_b/sqrt(n): DAM theta law vs Gaussian")
    print("  complex Gaussian: rk_complex=2.0  rk6=6.0  re_kurt=3.0 ; DAM heavy tail -> >>")
    print("="*74)
    for (p,n) in [(40009,8),(100003,16),(100003,32),(1000003,32),(1000003,64),(2000003,64)]:
        r=test_A(p,n)
        print(f"  n={n:3d} p={p:8d}: rk_c={r['rk_complex']:.4f} rk6={r['rk6']:6.3f} "
              f"re_kurt={r['re_kurt']:.3f} max={r['maxz']:.2f} tail={r['tail']}")
    print("\n"+"="*74)
    print("TAIL LAW (empirical, Rayleigh e^-R^2, DAM R^-4) -- thin prize regime p>>n^3")
    print("="*74)
    for (p,n) in [(1048583,16),(1000003,32),(2000003,64)]:
        print(f"  n={n} p={p} (p/n^3={p/n**3:.0f}): {test_tail(p,n)}")
    print("\n"+"="*74)
    print("TEST B -- sup-norm descent ratios (contraction needs ~sqrt2=1.414 each level)")
    print("="*74)
    for (p,n) in [(1000003,64),(2000003,64)]:
        print(f"  n={n} p={p}: {test_B(p,n)}")
    print("\n"+"="*74)
    print("TEST C -- Poisson/theta self-duality: does the dual sum get SHORTER?")
    print("="*74)
    for (p,n) in [(2003,16),(10007,16)]:
        print(f"  n={n} p={p}: {test_C(p,n)}")
