#!/usr/bin/env python3
"""
Verify the Garcia-Lorenz-Todd Theorem 4 V4 identity against my periods, and extract the
Betti/Hasse-Weil structure of the deep moment.  GLT: d = #periods = (p-1)/k, k = subgroup size.
In MY notation: subgroup mu_n has order n => their k=n, their d = m=(p-1)/n.
V4(p) = sum_s |eta_s|^4 (over d=m periods).
GLT Thm4 leading: V4 ~ (1/d^3)[(d-1)(d^2-3d+3) p^2 + 4(d-1)(d-2) p^{3/2} + ...].

The Hasse-Weil error term 4(d-1)(d-2)p^{3/2}/d^3 ~ 4 p^{3/2}/d = 4 (mn)^{3/2}/m = 4 n^{3/2} m^{1/2}.
This is the GENUS-(d-1)(d-2)/2 Fermat-curve error.  For V_{2r} the variety is a degree-d
hypersurface in 2r vars; its Betti number ~ d^{2r-1}, error ~ d^{2r-1} p^{(2r-1)/2} -> the wall.

We check the V4 identity holds and report kappa_2 = V4/(m * 3 * n^2).
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s
def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None
def find_prime(n, beta):
    lo=int(n**beta); p=lo+(1-lo)%n
    while p<int(n**(beta+0.6)):
        if is_prime(p): return p
        p+=n
    return None

print("GLT Thm4 V4 identity + Hasse-Weil error scaling check (d=m periods, k=n subgroup)")
for n in (8,16,32):
    p=find_prime(n,4.0)
    g0=gen_Fp_star(p)
    m=(p-1)//n
    gen_mu=pow(g0,(p-1)//n,p)
    mu=[pow(gen_mu,i,p) for i in range(n)]
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=np.array([sum(cmath.exp(2j*cmath.pi*(b*x%p)/p) for x in mu).real for b in reps])
    V4=float(np.sum(etas**4))
    d=m
    # GLT Theorem 1(a): for FIXED k=n with 2|k and (p,k) circular, V4 = 3p(k-1) - k^3 EXACTLY (no error).
    glt1 = 3*p*(n-1) - n**3 if (n%2==0) else p*(2*n-1) - n**3   # Thm1(a)/(b)
    kap2=V4/(m*3*n**2)
    print(f" n={n} p={p} m={m}: V4(meas)={V4:.1f}  GLT-Thm1 [3p(k-1)-k^3]={glt1}  diff={V4-glt1:.2e}")
    print(f"        kappa_2 = V4/(3 m n^2) = {kap2:.5f}   (char-0/Gaussian = 1; <1 = bounded-support sub-Gaussian)")
print()
print("GLT Theorem 1 gives V4 EXACTLY (zero error) for fixed k = subgroup size -- this IS the proven r=2")
print("cumulant. It is a 2-variable Fermat CURVE count (genus (m-1)(m-2)/2, Plucker), needing circularity.")
print("For r>=3 the variety is a (2r)-var degree-m hypersurface; Betti ~ m^{2r-1}, the sqrt(p)*Betti error")
print("overwhelms the diagonal => deep-moment wall. The deep cumulants ARE Betti point counts (not non-Betti).")
