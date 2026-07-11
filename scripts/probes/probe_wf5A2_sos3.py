#!/usr/bin/env python3
"""wf-A2: rigorous degree-vs-value scan. The honest Lasserre-on-circle relaxation constrains
moments y_0..y_d via a (d+1)x(d+1) PSD Toeplitz AND requires the moment sequence to extend to a
genuine measure -> equivalently we impose PSD Toeplitz of size (D+1), D=max exponent, and read
the value as a function of how many moments we 'see'. The correct degree-d UPPER bound on
max Re eta(z) (Lasserre hierarchy on the unit circle) is:
   min_t t s.t. t*delta_0 - c is in the cone of degree-d nonneg trig polys (Fejer-Riesz),
where c_k = coefficient of z^k in eta = 1 if k in mu_n (mod p, lifted to 0..p-1), else 0.
A degree-d nonneg trig poly has Fourier support in [-d,d]. For t*delta_0 - eta to be expressible
we need eta's support inside [-d,d] (mod the circle). Since mu_n mod p occupies residues up to
p-1, NO finite d < (spread) can even REPRESENT eta -> the only valid certificates need
d >= ceil(spread/2) where spread = (max gap structure). MEASURE the minimal d that makes the
SDP BOUNDED, and the value there."""
import sympy, math
import numpy as np
import cvxpy as cp

def subgroup(p, n):
    g = int(sympy.primitive_root(p)); zeta = pow(g,(p-1)//n,p)
    return np.array([pow(zeta,j,p) for j in range(n)],dtype=np.int64)

def true_M_re(p,n):
    mu=subgroup(p,n); b=np.arange(1,p); ph=np.outer(mu,b)%p
    eta=np.exp(2j*math.pi*ph/p).sum(axis=0)
    return float(np.abs(eta).max()), float(eta.real.max())

def lasserre_circle(p,n,d):
    """degree-d Lasserre on circle: pseudo-moments y_{-D..D}, (d+1) PSD Toeplitz; objective
    Re sum_{j} y_{e_j}. To make finite we cap D=d (moments beyond d set to 0 = degree-d
    truncation, the standard hierarchy). Then objective only counts e_j <= d."""
    e=subgroup(p,n).astype(int)
    y=cp.Variable(d+1,complex=True)
    cons=[y[0]==1]
    T=cp.bmat([[y[abs(a-b)] if a>=b else cp.conj(y[abs(a-b)]) for b in range(d+1)] for a in range(d+1)])
    cons+=[T>>0]
    inrange=[int(ej) for ej in e if ej<=d]
    if not inrange:  # objective references nothing -> degree-d sees only constant term
        return 0.0,"trivial(0)",len(inrange),len(e)
    obj=cp.real(cp.sum([y[k] for k in inrange]))
    prob=cp.Problem(cp.Maximize(obj),cons)
    prob.solve(solver=cp.SCS,verbose=False,max_iters=30000)
    return prob.value,prob.status,len(inrange),len(e)

if __name__=="__main__":
    for n,p in [(8,89),(16,193)]:
        if (p-1)%n: continue
        M,Mre=true_M_re(p,n)
        print(f"=== n={n} p={p} m={(p-1)//n}  |eta| max={M:.3f}  Re eta max={Mre:.3f}  target sqrt(nlog)={math.sqrt(n*math.log(p/n)):.3f} ===")
        for d in (2,4,8,16,32,64,p-1):
            if d>=p: d=p-1
            v,st,nin,ntot=lasserre_circle(p,n,d)
            print(f"  d={d:3d}: SoS_val={v:8.3f} [{st[:6]}]  exponents_seen={nin}/{ntot}")
            if d==p-1: break
