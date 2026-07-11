#!/usr/bin/env python3
"""Line-list size in [halfJ,J) for mu_n RS at LARGE p (Sidon window p>2^n infeasible
to fully enumerate, but we sample large p with n|p-1 and use interpolation, not
codeword enumeration).

Key idea: a codeword of RS[deg<k] agreeing with a word `line` on >= t >= k coords
is UNIQUELY determined by any k of those agreement coords (interpolation). So the
line-list-size at radius t (>=k) = number of DISTINCT codewords obtained by:
  for each line point u0+g*u1, for each size-k subset S of coords, interpolate the
  unique deg<k poly through (x_i, line_i)_{i in S}, check it agrees with line on >=t.
We dedup by the polynomial's coefficient tuple. This is exact and works for huge p.

We compare the small subgroup (u1 drawn from mu_n -> full support, Sidon) vs a
RANDOM full-support u1 (entries random nonzero, NOT mu_n) to see if Sidon matters.
"""
import itertools, math, random

def is_prime(p):
    if p<2: return False
    if p%2==0: return p==2
    d=3
    while d*d<=p:
        if p%d==0: return False
        d+=2
    return True

def find_prime(n, lo):
    p=lo+1
    while True:
        if is_prime(p) and (p-1)%n==0: return p
        p+=1

def find_gen(p):
    phi=p-1; m=phi; facs=set(); d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g

def interp_coeffs(pts, p):
    # Lagrange interpolation of deg<k poly through pts=[(x_i,y_i)], return coeff tuple deg<k.
    # returns tuple of k coeffs (constant..leading). Use Newton/Lagrange over F_p.
    k=len(pts)
    # build coefficient vector via Lagrange
    coeffs=[0]*k
    for i,(xi,yi) in enumerate(pts):
        # basis poly L_i = prod_{j!=i} (X - xj)/(xi - xj)
        num=[1]  # poly coeffs low..high
        den=1
        for j,(xj,_) in enumerate(pts):
            if j==i: continue
            # multiply num by (X - xj)
            new=[0]*(len(num)+1)
            for d,c in enumerate(num):
                new[d]=(new[d]-c*xj)%p
                new[d+1]=(new[d+1]+c)%p
            num=new
            den=(den*(xi-xj))%p
        inv=pow(den,p-2,p)
        scale=(yi*inv)%p
        for d in range(len(num)):
            if d<k: coeffs[d]=(coeffs[d]+num[d]*scale)%p
    return tuple(coeffs)

def eval_poly(coeffs, x, p):
    r=0
    for c in reversed(coeffs):
        r=(r*x+c)%p
    return r

def line_list_size(u0,u1,t,k,mu,p):
    n=len(mu)
    found=set()
    idxs=list(range(n))
    for g in range(p):
        line=[(u0[i]+g*u1[i])%p for i in range(n)]
        # candidate codewords: interpolate through each size-k subset, check agreement >= t
        for S in itertools.combinations(idxs,k):
            if len(set(line[i] for i in S))<0: pass
            pts=[(mu[i],line[i]) for i in S]
            # need distinct x's (they are, mu distinct)
            cf=interp_coeffs(pts,p)
            if cf in found: continue
            agree=sum(1 for i in range(n) if eval_poly(cf,mu[i],p)==line[i])
            if agree>=t:
                found.add(cf)
    return len(found)

def main(n, k, p=None, samples=4, seed=0):
    if p is None: p=find_prime(n, max(200,4*n))
    g=find_gen(p); w=pow(g,(p-1)//n,p)
    mu=[pow(w,i,p) for i in range(n)]
    assert 0 not in mu and len(set(mu))==n
    rho=k/n; J=1-math.sqrt(rho); halfJ=J/2
    print(f"\nn={n} k={k} p={p} rho={rho:.4f} halfJ={halfJ:.4f} J={J:.4f}")
    random.seed(seed)
    muset=mu
    nonzero=[x for x in range(1,p)]
    print(f"  {'t':>3} {'delta':>6} {'L_mu':>6} {'L_rand':>7} {'a^2-ne':>7} region   "
          f"(C(n,k)={math.comb(n,k)})")
    # restrict to interesting t (around the window) to keep cost down: t>=k
    for t in range(n, k-1, -1):
        d=1-t/n
        a=2*t-n; e=k-1; den=a*a-n*e
        reg='<halfJ' if d<halfJ-1e-9 else ('[halfJ,J)' if d<J-1e-9 else '>=J')
        Lmu=0; Lrand=0
        for _ in range(samples):
            u0=[random.randrange(p) for _ in range(n)]
            u1mu=[random.choice(mu) for _ in range(n)]   # in mu_n: Sidon, full support
            u1rnd=[random.choice(nonzero) for _ in range(n)]  # full support, NOT mu_n
            Lmu=max(Lmu, line_list_size(u0,u1mu,t,k,mu,p))
            Lrand=max(Lrand, line_list_size(u0,u1rnd,t,k,mu,p))
        print(f"  {t:>3} {d:>6.3f} {Lmu:>6} {Lrand:>7} {den:>7} {reg}")

if __name__=="__main__":
    # mu_8, the named instance, k=2 and k=3, large-ish p in Sidon-ish range
    main(8,2,samples=3)
    main(8,3,samples=3)
