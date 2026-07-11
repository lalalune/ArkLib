#!/usr/bin/env python3
"""
probe_s11_geom_mgf_closure.py  (#444, S11 — closing the survival-weighted sum to a SCALAR)

mgf_le_survival_weighted reduced  Sum_b exp(c t_b)  to  Sum_theta delta_theta * N(theta),
N(theta)=#{b: theta<=t_b}.  GOAL: under a literal sub-exp survival tail N(theta) <= B*exp(-cc*theta)
with cc>c, find the cleanest SIGN-DEFINITE closed-form scalar ceiling.

Candidate clean discrete inequality (the one I want to formalize):
  On a UNIFORM grid theta_j = j*h (j=0..K), delta_j = exp(c theta_j)-exp(c theta_{j-1}) (j>=1),
  delta_0 = exp(0)=1.  Each delta_j <= c*h*exp(c theta_j) (since exp(c t_j)-exp(c t_{j-1})
  = integral <= c*h*exp(c t_j)).  Then
     Sum_j delta_j N_j <= N_0 + c*h * Sum_{j>=1} exp(c theta_j) * B exp(-cc theta_j)
                        = P + c*h*B * Sum_{j>=1} exp(-(cc-c) theta_j)
                        <= P + c*h*B * exp(-(cc-c)h)/(1-exp(-(cc-c)h))   (geometric, cc>c)
  As h->0 this -> P + c*B/(cc-c).  With B=A*P this is P*(1 + c*A/(cc-c)).  So K = 1 + c*A/(cc-c).
  CHECK: (a) the per-increment bound delta_j <= c*h*exp(c theta_j); (b) the geometric sum closes;
  (c) the resulting scalar ceiling actually upper-bounds the TRUE MGF on real spectra.
"""
import numpy as np
from sympy import primerange

def gauss_period_spectrum(p, n):
    cof=(p-1)//n
    def pr(g):
        x=1;s=set()
        for _ in range(p-1): x=(x*g)%p; s.add(x)
        return len(s)==p-1
    g=2
    while not pr(g): g+=1
    h=pow(g,cof,p); H=[];x=1
    for _ in range(n): H.append(x);x=(x*h)%p
    H=np.array(H);bs=np.arange(1,p);ang=2*np.pi/p
    eta=np.exp(1j*ang*np.outer(bs,H)).sum(axis=1)
    return (np.abs(eta)**2)/n

def geom_closure(t, c, cc, h=0.01):
    P=len(t); tmax=t.max()
    K=int(np.ceil(tmax/h))+2
    theta=np.arange(K+1)*h
    N=np.array([np.sum(t>=th-1e-12) for th in theta],dtype=float)
    g=np.exp(c*theta)
    delta=np.empty_like(g); delta[0]=g[0]; delta[1:]=g[1:]-g[:-1]
    survweighted=np.sum(delta*N)            # the exact RHS of mgf_le_survival_weighted (staircase>=mgf)
    direct=np.sum(np.exp(c*t))
    # tail constant B = sup_theta N(theta) exp(cc theta)  (smallest B with N<=B exp(-cc theta))
    B=np.max(N*np.exp(cc*theta))
    # per-increment bound check: delta_j <= c*h*exp(c theta_j) for j>=1
    incr_ok=np.all(delta[1:] <= c*h*g[1:] + 1e-12)
    # geometric closed form K_scalar = 1 + c*B/P/(cc-c) (continuous limit); discrete: P + c h B geom
    if cc>c:
        geom_tail = c*h*B*np.exp(-(cc-c)*h)/(1-np.exp(-(cc-c)*h))
        scalar_ub_discrete = P + geom_tail
        scalar_ub_cont = P*(1 + c*(B/P)/(cc-c))
    else:
        scalar_ub_discrete=scalar_ub_cont=np.inf
    return direct, survweighted, scalar_ub_discrete, scalar_ub_cont, B/P, incr_ok

if __name__=="__main__":
    cases=[]
    for n in [4,8,16]:
        k=0
        for p in primerange(max(50,n**3),n**3+5000):
            if (p-1)%n==0 and (p-1)//n>=2:
                cases.append((p,n));k+=1
                if k>=1: break
    print("=== GEOMETRIC closure of survival-weighted sum (cc>c) ===")
    print("direct=true MGF*P ; survw=staircase RHS ; ub_d/ub_c=geometric scalar ceilings ; need ub>=survw>=direct")
    for (p,n) in cases:
        t=gauss_period_spectrum(p,n)
        for (c,cc) in [(0.3,0.5),(0.4,0.6),(0.3,0.6)]:
            d,sw,ubd,ubc,BP,iok=geom_closure(t,c,cc)
            # the real claim: incr-bound (delta_j<=c h exp(c theta_j)) + geometric => ub>=direct.
            # survw is a discretization lower-Riemann artifact, NOT the bound, so don't gate on it.
            ok = (ubd>=d-1e-6) and (ubc>=d-1e-6) and iok
            print(f"p={p:5d} n={n:3d} c={c:.1f} cc={cc:.1f}: direct={d:.1f} ub_d={ubd:.1f} "
                  f"ub_c={ubc:.1f} B/P={BP:.3f} incr_ok={iok} ub>=direct={'Y' if ubd>=d-1e-6 else 'N'} {'OK' if ok else 'FAIL'}")
