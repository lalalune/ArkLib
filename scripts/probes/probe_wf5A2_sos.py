#!/usr/bin/env python3
"""
wf-A2 lane (#444): orbit-reduced SoS / Lovasz-theta dual certificate for
M(n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x), mu_n = 2-power subgroup.

KEY STRUCTURAL FACT: eta_b are EXACTLY the eigenvalues of the Cayley graph
A = Cay(F_p, mu_n union -mu_n) (circulant of order p). lambda_2 = max over b!=0 of eta_b
(real part for symmetric set; full |eta_b| with the conjugate-symmetric set).

The Lovasz-theta-type / SoS upper bound on lambda_2 of a SYMMETRIC matrix:
  lambda_2(A) <= t  iff  there is a PSD certificate.
For a circulant, A = F* diag(eta) F, so this is trivial spectrally. The SoS QUESTION is:
can a LOW-DEGREE pseudo-distribution over the GROUP certify a t << n? i.e. is there a
degree-d SoS proof of  eta_b <= t  for all b!=0, using only the relation x^n=1 (mu_n is the
n-th roots) and the field. Pre-screen: solve the orbit-reduced moment SDP at small degree d.

The orbit-reduced SDP for max_{b} |sum_{j} omega^{b g_j}| where g_j enumerates mu_n:
this is a trig moment / Chebyshev problem. We solve the degree-d SDP:
  maximize  <C, X>  s.t. X >= 0, moment/Toeplitz consistency, X_00 = 1
whose optimum upper-bounds (or equals) the true max, and read whether a SMALL d certifies sqrt(n log).
"""
import sympy, math
import numpy as np
import cvxpy as cp

def subgroup(p, n):
    g = int(sympy.primitive_root(p))
    zeta = pow(g, (p-1)//n, p)
    return np.array([pow(zeta, j, p) for j in range(n)], dtype=np.int64)

def true_M(p, n):
    mu = subgroup(p, n)
    b = np.arange(1, p, dtype=np.int64)
    ph = np.outer(mu, b) % p
    eta = np.exp(2j*math.pi*ph/p).sum(axis=0)
    return float(np.abs(eta).max()), float(np.abs(eta).real.max() if False else np.abs(eta).max())

# ---- The degree-d SoS / moment relaxation ----
# We treat z = e_p(b) as a free point on the unit circle. eta(z) = sum_j z^{g_j} is a
# LAURENT polynomial in z (exponents = elements of mu_n as integers mod p). The SoS upper bound
# on max_{|z|=1} Re(eta(z)) at degree d uses the Toeplitz/Fejer-Riesz dual:
#   min  t  s.t.  t - Re(eta(z)) = |sigma(z)|^2 on |z|=1  with deg sigma <= d  (sum of hermitian sq)
# This is a trig-polynomial nonnegativity -> PSD Toeplitz. The exponents of eta are SPREAD over
# 0..p-1 (mu_n mod p), so degree-d certificate needs d >= (max exponent)/1 ~ p. That is the wall:
# the SoS degree to certify is governed by the SPECTRAL SPREAD of mu_n mod p, not by n.
# We MEASURE: the minimal degree-d certificate value vs d, vs sqrt(n log(p/n)).

def sos_value_degree(p, n, d, ngrid=4000):
    """Upper bound on max_{b} Re(eta_b) via degree-d nonneg-trig-poly (Fejer) certificate,
    discretized. Returns the certified t. We use the primal grid SDP dual:
    find probability measure mu on circle maximizing E[Re eta] with moments up to d matched to a
    PSD Toeplitz (pseudo-moment) matrix. Optimum = degree-d SoS bound (Lasserre on the circle)."""
    # exponents of eta over Z (mu_n elements as integers in 0..p-1)
    e = subgroup(p, n).astype(np.int64)
    # pseudo-moments y_k for k = -(big)..(big). We only need moments at the exponents +/- e and
    # for the PSD Toeplitz of size (d+1): y_0..y_d. But eta has exponents up to p-1 >> d.
    # => to even WRITE the objective at degree d we need pseudo-moments y_{e_j}. If e_j > d the
    # moment is OUTSIDE the certificate -> unconstrained -> SDP unbounded / vacuous.
    # This directly exposes whether low-degree d works. We allow moments up to D = max needed.
    D = int(e.max())
    # PSD Toeplitz pseudo-moment of size (d+1): M[a,b] = y_{a-b}, needs y_0..y_d.
    # Objective uses y_{e_j}; if e_j>d these are FREE vars only tied by being a valid moment
    # sequence iff the FULL Toeplitz up to D is PSD. So the honest low-degree relaxation only
    # constrains via size-(d+1) Toeplitz; moments y_k for k>d appear in objective but are free
    # except they must be consistent with SOME extension. Lasserre: only size-(d+1) block PSD.
    y = cp.Variable(D+1, complex=True)
    cons = [y[0] == 1]
    # size-(d+1) PSD Toeplitz
    T = cp.bmat([[ y[abs(a-bb)] if a>=bb else cp.conj(y[abs(a-bb)]) for bb in range(d+1)] for a in range(d+1)])
    cons += [T >> 0]
    # objective: Re sum_j y_{e_j}  (each e_j in 1..D). y_{e_j} free if e_j>d.
    obj = cp.real(cp.sum([y[int(ej)] for ej in e]))
    prob = cp.Problem(cp.Maximize(obj), cons)
    try:
        prob.solve(solver=cp.SCS, verbose=False, max_iters=20000)
    except Exception as ex:
        return None, str(ex)
    return (prob.value, prob.status)

if __name__ == "__main__":
    # thin-ish primes p = n*m+1 prime, m as large as feasible for small SDP
    cases = [(8, 17), (8, 41), (16, 97), (8, 89), (16, 193)]
    for n, p in cases:
        if not sympy.isprime(p) or (p-1)%n: 
            print(f"skip n={n} p={p}"); continue
        M, _ = true_M(p, n)
        line = f"n={n:3d} p={p:5d} m={(p-1)//n:4d} | trueM={M:7.3f}  sqrt(n*log(p/n))={math.sqrt(n*math.log(p/n)):6.3f} | "
        for d in (2, 4, 8):
            if d >= p: continue
            v, st = sos_value_degree(p, n, d)
            line += f"d={d}:{v:.2f}({st[:4]}) " if v is not None else f"d={d}:FAIL "
        print(line)
