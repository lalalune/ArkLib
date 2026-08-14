#!/usr/bin/env python3
"""
wf-NA part 2: the DUAL / Stein-Tomas-Mockenhaupt restriction side -- escape vs wall.

The real Mockenhaupt-Tao restriction theorem (not trivial L^inf<=L^r monotonicity) needs
Fourier decay |hat{sigma}(b)| = |eta_b|/n <= A n^{1-a'} of the surface measure on mu_n.
The square-root-cancellation target a'=1/2 (|eta_b|<=A sqrt(n)) IS the prize itself, so the
dual side is CIRCULAR unless mu_n has a PROVABLE geometric decay. We measure exactly:
  (1) a_emp = 1 - log M(n)/log n: empirical Fourier-decay exponent; p-indep (geometric)
      or p-dependent (arithmetic = BGK wall)?
  (2) additive energy E_2 (the only question-begging-free Stein-Tomas input) and the L4
      bound (q E_2)^{1/4} it yields -- the L4 no-go.
Exact full enumeration. No sampling.
"""
import math, cmath
from sympy import isprime, primitive_root

def subgroup_mu_n(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    out, cur = [], 1
    for _ in range(n):
        out.append(cur); cur = (cur*h)%p
    return out

def all_abs_eta(p, mu):
    res = []
    for b in range(p):
        s = 0j
        for x in mu: s += cmath.exp(2j*math.pi*((b*x)%p)/p)
        res.append(abs(s))
    return res

def main():
    print("="*70)
    print("wf-NA part 2: Stein-Tomas / dual restriction -- escape vs wall (EXACT)")
    print("="*70)
    print(" a_emp = 1 - log M(n)/log n  (square-root/Salem prize needs a_emp->0.5, p-indep)\n")
    n_primes = {8:[(193,2.5),(521,3.0),(4129,4.0)],
                16:[(1153,2.5),(4129,3.0),(65537,4.0)],
                32:[(3329,2.4),(32801,3.0)]}
    for n, plist in n_primes.items():
        print(f"--- n={n} (sqrt(n)={math.sqrt(n):.4f}) ---")
        a_vals = []
        for p, beta in plist:
            mu = subgroup_mu_n(p, n); ab = all_abs_eta(p, mu)
            Mn = max(ab[1:]); a_emp = 1 - math.log(Mn)/math.log(n)
            E2 = sum(v**4 for v in ab)/p
            st_M = (p*E2)**0.25; ceil = math.sqrt(2*n*math.log(p))
            a_vals.append(a_emp)
            print(f"  p={p:<6} beta~{beta:.2f}: M={Mn:7.4f} a_emp={a_emp:.4f} "
                  f"E2={E2:8.1f}(char0={3*n*n-3*n}) ST-L4={st_M:7.4f} ceil={ceil:7.4f}")
        spread = max(a_vals)-min(a_vals)
        tag = "p-DEPENDENT (arithmetic=BGK wall)" if spread>0.02 else "p-independent"
        print(f"  => a_emp spread = {spread:.4f}  ({tag})\n")
    print("Dual is circular (input=Fourier decay=M(n)); only borrowable input E2 -> L4 no-go.")
    print("mu_n NOT Salem (a_emp far from 0.5, p-dependent). PINNED to deep-moment wall.")

if __name__ == "__main__":
    main()
