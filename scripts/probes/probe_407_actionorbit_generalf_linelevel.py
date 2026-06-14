#!/usr/bin/env python3
"""
SALVAGE test: for general-f, the per-line orbit fails, but does the LINE-LEVEL equivariance
hold?  i.e. dilation D_mu maps line(base, f) -> line(base', f o D_mu) with the SAME bad-gamma
count (|bad(f)| = |bad(f o D_mu)|)?  This is explainableScalars_comp_aut. If yes: the structure
that survives for general-f is line-orbit invariance (count distinct line-CLASSES), NOT a
per-line gamma-orbit bound.

Also: does dilation D_mu act on the bad-gamma set of a general-f line as a fixed REPARAMETRIZATION
(gamma -> c*gamma for SOME c depending on f) when f is a single monomial vs general?
"""
import itertools
from math import gcd, sqrt

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def prime_1_mod_n(n, lo):
    p=(lo|1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=2
def find_gen(p,n):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//n,p)
        if pow(w,n,p)==1 and all(pow(w,n//q,p)!=1 for q in (2,3,5,7) if n%q==0):
            return w
    raise RuntimeError
def best_agreement(H, vals, p, k):
    n=len(H); best=0
    for sub in itertools.combinations(range(n),k):
        bx=[H[i] for i in sub]; by=[vals[i] for i in sub]
        def interp(x):
            tot=0
            for j in range(k):
                num=by[j]%p; den=1
                for l in range(k):
                    if l!=j:
                        num=num*((x-bx[l])%p)%p
                        den=den*((bx[j]-bx[l])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            return tot
        cnt=sum(1 for i in range(n) if interp(H[i])==vals[i]%p)
        if cnt>best:
            best=cnt
            if best==n: break
    return best
def bad_gammas(H, base, fvals, p, k, thr):
    bad=set()
    for g in range(1,p):
        vals=[(base[i]+g*fvals[i])%p for i in range(len(H))]
        if best_agreement(H,vals,p,k)>=thr: bad.add(g)
    return bad

n,k=8,2; p=prime_1_mod_n(n,400)
w=find_gen(p,n); H=[pow(x:=pow(w,i,p),1,p) for i in range(n)]
H=[pow(w,i,p) for i in range(n)]
# index of mu*x in H: dilation by w^1 permutes H by index+1 mod n
# A direction vector f over H. f o D_mu means: (f o D_mu)(x_i)=f(mu*x_i)=f(x_{i+1}).
# base = x^7 vector
a=7
base=[pow(x,a,p) for x in H]
t=3  # interior
print(f"n={n} k={k} p={p} t={t} (interior d={1-t/n:.3f}); LINE-LEVEL equivariance for general f", flush=True)
def fvec_from_exps(exps): return [sum(c*pow(x,e,p) for (e,c) in exps)%p for x in H]
for desc,exps in [("MONO x^2",[(2,1)]),("GEN x^2+x^3",[(2,1),(3,1)]),("GEN x^2+3x^4",[(2,1),(3,1),(4,3)])]:
    f=fvec_from_exps(exps)
    # base after dilation: base(mu x)=x^a evaluated at mu x = mu^a * base. As a vector it's
    # the shift of base by one index (times nothing since it's still in code-space). We use the
    # exact composed line: u0' = base shifted, f' = f shifted (index i -> i+1).
    base_sh=[base[(i+1)%n] for i in range(n)]
    f_sh   =[f[(i+1)%n]    for i in range(n)]
    b0=bad_gammas(H, base, f, p, k, t)
    b1=bad_gammas(H, base_sh, f_sh, p, k, t)
    print(f"  {desc:14}: |bad(line)|={len(b0):3d}  |bad(D_mu line)|={len(b1):3d}  equal={len(b0)==len(b1)}", flush=True)
print("DONE", flush=True)
