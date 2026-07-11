#!/usr/bin/env python3
"""
wf-NA: Finite-field restriction / extension estimates for mu_n in F_q.

M(n) = max_{b!=0} |Sum_{x in mu_n} e_p(b x)| is the L-infinity norm of the EXTENSION
operator (E f)(b) = Sum_{x in mu_n} f(x) e_p(b x) applied to f = 1, i.e. the finite-field
restriction problem for the multiplicative-subgroup "variety" mu_n in F_q.

KEY HONESTY TEST. For EVEN r = 2s:
    ||E1||_{L^r(F_q)}^r = Sum_{b in F_q} |eta_b|^{2s} = q * E_s   (deep moment).
So the even-r extension norm IS the deep-moment object. Restriction can only escape the
moment wall via INTERPOLATION between exponents or the dual R*(2->r') with r'<2. We test:
  (A) normalized restriction constant c_r = ||E1||_{L^r}/q^{1/r}.
  (B)/(D) best moment M-bound vs best restriction(L^r) bound; sub-trivial?
  Fourier-decay exponent kappa = log M(n)/log n.

Exact arithmetic (full enumeration over F_q). No sampling on any verdict.
"""
import math, cmath
from sympy import isprime, primitive_root

def subgroup_mu_n(p, n):
    assert (p - 1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    out, cur = [], 1
    for _ in range(n):
        out.append(cur); cur = (cur * h) % p
    assert len(set(out)) == n
    return out

def all_abs_eta(p, mu):
    res = []
    for b in range(p):
        s = 0j
        for x in mu:
            s += cmath.exp(2j*math.pi*((b*x)%p)/p)
        res.append(abs(s))
    return res

def extension_norms(p, ab, r_list):
    out = {}
    for r in r_list:
        s = sum(ab[b]**r for b in range(1, p))
        out[r] = s ** (1.0/r)
    return out

def best_moment_Mn(p, ab, s_max):
    best, best_s = None, None
    for s in range(1, s_max+1):
        tot = sum(ab[b]**(2*s) for b in range(1, p))
        val = tot ** (1.0/(2*s))
        if best is None or val < best:
            best, best_s = val, s
    return best, best_s

def find_primes(n, betas, count=2):
    out = {}
    for beta in betas:
        target = int(round(n**beta))
        p = target - (target % n) + 1
        if p < target: p += n
        found, guard = [], 0
        while len(found) < count and guard < 2_000_000:
            if isprime(p): found.append(p)
            p += n; guard += 1
        out[beta] = found
    return out

def main():
    print("="*70)
    print("wf-NA: finite-field RESTRICTION / EXTENSION norms for mu_n in F_q")
    print("="*70)
    configs = [(8,[2.5,3.0,4.0]),(16,[2.5,3.0,4.0]),(32,[2.0,2.5,3.0])]
    for n, betas in configs:
        print(f"\n### n = {n}  (sqrt(n)={math.sqrt(n):.4f})")
        primes = find_primes(n, betas)
        r_family = [4,6,8,10,12,16,20]; s_max = 10
        for beta, plist in primes.items():
            for p in plist:
                mu = subgroup_mu_n(p, n)
                ab = all_abs_eta(p, mu)
                Mn = max(ab[1:])
                kappa = math.log(Mn)/math.log(n)
                norms = extension_norms(p, ab, r_family)
                interp = min(norms.values()); interp_r = min(norms, key=lambda r: norms[r])
                mom, mom_s = best_moment_Mn(p, ab, s_max)
                ceiling = math.sqrt(2*n*math.log(p))
                gap = interp - mom
                v = "RESTRICTION BEATS MOMENTS" if gap<-1e-9 else ("EQUAL (collapse)" if abs(gap)<1e-6 else "moments win")
                print(f"  p={p:<6} beta~{beta:.2f}: M={Mn:.4f} kappa={kappa:.4f} "
                      f"mom-bound={mom:.4f}(s={mom_s}) restr-bound={interp:.4f}(r={interp_r}) "
                      f"ceil={ceiling:.4f} gap={gap:+.2e} => {v}")
    print("\nEven-r extension norm = q*E_{r/2} exactly => collapse to deep-moment wall.")

if __name__ == "__main__":
    main()
