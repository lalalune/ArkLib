#!/usr/bin/env python3
"""
#407 cumulant-deep-nonbetti  --  (i) VERIFY the exact identity kappa_r <-> energy defect,
                                  (ii) test cross-parity self-improvement on kappa_r.

(i) IDENTITY.  Sum_{b in F_q} |eta_b|^{2r} = q E_r,  E_r=#{(x,y) in mu_n^{2r}: sum x = sum y}.
    eta_0 = n.  Distinct nonzero periods eta_i, each mult n:  n Sum_i eta_i^{2r} = q E_r - n^{2r}.
    So  Sum_i eta_i^{2r} = (q E_r - n^{2r})/n,  and kappa_r = Sum_i eta_i^{2r}/(m (2r-1)!! n^r).
    Char-0 (Lam-Leung): E_r^{C} = (2r-1)!! n^r  (for n=2^a; antipodal-pair matchings).  So with
    E_r = E_r^C + defect_r,   kappa_r = 1  <=>  defect_r exactly compensates the n^{2r}/n - boundary.
    We CHECK numerically that kappa_r computed from periods == kappa_r computed from E_r-defect.

(ii) CROSS-PARITY SELF-IMPROVEMENT.  The measured structural feature: ~96-100% of F_q-defects (the
    extra solutions Sum x = Sum y mod p NOT holding over C) satisfy A = -g B  (g a fixed unit).
    Self-improvement HOPE: if defect_r is governed by |S_0 cap (-g)S_0| (subset-sum image meets its
    dilate), and this incidence is itself bounded by a LOWER cumulant (bootstrap), then kappa_r at
    depth r is controlled by kappa_{r'} at r'<r -> a descent closing the deep moments.
    TEST: is defect_r / (char-0 term) MULTIPLICATIVELY bounded by (defect_{r-1}/char0)^{theta},
    theta<1 (a contraction)?  Or does defect_r grow FASTER than any power of defect_{r-1} (no descent)?
    We track g_r := defect_r/E_r^C across r and primes; a contraction needs g_r <= g_{r-1}^theta.
"""
import cmath, math
import numpy as np
from itertools import product

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

def Er_mod_p(p, mu, r):
    """E_r = #{(x_1..x_r,y_1..y_r) in mu^{2r}: sum x = sum y mod p}.  Brute for small n,r."""
    n=len(mu)
    # count via convolution: c[v]=#{r-tuples summing to v mod p}; E_r = sum_v c[v]^2
    from collections import defaultdict
    c=defaultdict(int); c[0]=1
    for _ in range(r):
        nc=defaultdict(int)
        for v,cnt in c.items():
            for x in mu:
                nc[(v+x)%p]+=cnt
        c=nc
    return sum(cnt*cnt for cnt in c.values())

def Er_char0(n,r):
    # (2r-1)!! n^r   (n=2^a antipodal)
    df=1
    for i in range(1,r+1): df*=(2*i-1)
    return df*n**r

print("="*100)
print("(i) IDENTITY CHECK + (ii) cross-parity defect growth (contraction test)")
print("="*100)
for n in (8,16):
    p=find_prime(n,4.0)
    g0=gen_Fp_star(p)
    m=(p-1)//n
    gen_mu=pow(g0,(p-1)//n,p)
    mu=[pow(gen_mu,i,p) for i in range(n)]
    # periods
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=np.array([sum(cmath.exp(2j*cmath.pi*(b*x%p)/p) for x in mu).real for b in reps])
    print(f"\n--- n={n} p={p} m={m} ---")
    print("  r | kappa(periods) | kappa(via E_r) | E_r | E_r^C | defect_r | g_r=def/E^C | g_r/g_{r-1}^? ")
    prev_g=None
    for r in range(1, 6):
        df=1
        for i in range(1,r+1): df*=(2*i-1)
        kap_per = float(np.sum(etas**(2*r)))/(m*df*n**r)
        Er=Er_mod_p(p,mu,r)
        kap_E = (p*Er - n**(2*r))/n/(m*df*n**r)
        E0=Er_char0(n,r)
        defect=Er-E0
        g=defect/E0 if E0 else float('nan')
        ratio=""
        if prev_g is not None and prev_g>0 and g>0:
            theta=math.log(g)/math.log(prev_g) if prev_g!=1 else float('nan')
            ratio=f"theta={theta:.2f}"
        print(f"  {r} | {kap_per:13.5f} | {kap_E:13.5f} | {Er:>10d} | {E0:>10d} | {defect:>9d} | {g:.3e} | {ratio}")
        prev_g=g
print()
print("IDENTITY ok if kappa(periods)==kappa(via E_r). CONTRACTION (self-improve) would need theta>1")
print("(g_r = g_{r-1}^theta with theta>1 => defect ratio SHRINKS super-linearly => descent closes).")
print("theta<1 or g_r growing => no cumulant descent; defect is the energy excess = the SAME wall.")
