#!/usr/bin/env python3
"""
Door-(iv) Lane 1 follow-up — does a NON-energy small-ball functional of the phase set
A_b = {b*y mod p : y in mu_n} carry the sqrt-cancellation, or is it ENERGY-EQUIVALENT
(hence already capped at the BGK wall)?

Decisive test. For a fixed prime/n, compute over ALL coset-representative b:
  - |eta_b|                              (the target sup object)
  - C_b = max-window-count at scale p/n  (a small-ball / concentration functional, NON-energy on its face)
  - the additive-energy proxy E_b is NOT what we test; we test whether C_b is a
    DETERMINISTIC FUNCTION of |eta_b| (=> energy-equivalent, dead) or carries independent info.

KEY discriminator: a genuinely-new door-(iv) lever must be NOT monotone-determined by |eta|.
We measure rank-correlation(|eta_b|, C_b) and, more importantly, whether the WORST-b for C_b
coincides with the worst-b for |eta| (if C is just a repackaging of eta, argmax coincides and
C is monotone in eta => no new info => the small-ball route collapses to the sup-norm itself).

Also: scaling law. If C_worst grows like sqrt(n*log) it could in principle be the prize object;
if it grows linearly OR is pinned to |eta| it's dead. Sweep n=16..256.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta):
    target=int(round(n**beta)); k0=max(2,target//n)
    for dk in range(0,400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n and is_prime(p): return p
    return None

def subgroup(p,n):
    pm1=p-1; f={}; m=pm1; d=2
    while d*d<=m:
        while m%d==0: f[d]=1; m//=d
        d+=1
    if m>1: f[m]=1
    def isg(g):
        return all(pow(g,pm1//q,p)!=1 for q in f)
    g=2
    while not isg(g): g+=1
    h=pow(g,pm1//n,p); mu=[]; c=1
    for _ in range(n): mu.append(c); c=c*h%p
    return mu

def eta(b,mu,p):
    return abs(sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in mu))

def winmax(A,p,w):
    A=sorted(A); n=len(A); ext=A+[a+p for a in A]; best=0; j=0
    for i in range(n):
        while j<i+n and ext[j]<A[i]+w: j+=1
        best=max(best,j-i)
    return best

def spearman(xs,ys):
    def rank(v):
        s=sorted(range(len(v)),key=lambda i:v[i]); r=[0]*len(v)
        for k,i in enumerate(s): r[i]=k
        return r
    rx=rank(xs); ry=rank(ys); n=len(xs)
    d2=sum((rx[i]-ry[i])**2 for i in range(n))
    return 1-6*d2/(n*(n*n-1)) if n>1 else 0.0

def main():
    random.seed(7)
    print("=== small-ball functional vs |eta|: energy-equivalent or new? ===")
    print(f"{'n':>4} {'p':>11} {'M':>8} {'M/sqn':>7} {'Cworst':>7} {'Cworst/sqn':>10} "
          f"{'argmax_eq':>9} {'spearman(eta,C)':>15}")
    for n,beta in [(16,4.0),(32,4.0),(64,4.0),(128,4.0),(256,4.0)]:
        p=find_prime(n,beta)
        if p is None: continue
        mu=subgroup(p,n)
        w=p//n
        # representatives: eta is constant on b*mu_n cosets. number of cosets = (p-1)/n,
        # too many for large p; sample coset reps deterministically + the true worst region.
        reps=set()
        cur=1
        # take b across a spread; dedup by coset via b*mu_n min-element canonical form is costly,
        # so just sample a few thousand b and rely on the |eta|-coset invariance for stats.
        sample = list(range(1,min(p,2500)))
        if p>2500:
            sample += [random.randrange(1,p) for _ in range(2500)]
        sample=list(dict.fromkeys(sample))
        etas=[]; Cs=[]
        for b in sample:
            e=eta(b,mu,p)
            A=[(b*y)%p for y in mu]
            C=winmax(A,p,w)
            etas.append(e); Cs.append(C)
        iM=max(range(len(etas)),key=lambda i:etas[i])
        iC=max(range(len(Cs)),key=lambda i:Cs[i])
        M=etas[iM]; Cworst=Cs[iC]
        sqn=math.sqrt(n)
        rho=spearman(etas,Cs)
        # argmax_eq: does C's argmax coincide with eta's argmax (same b)?
        argmax_eq = "YES" if sample[iM]==sample[iC] else f"no(Cat_eta={Cs[iM]},max={Cworst})"
        print(f"{n:>4} {p:>11} {M:>8.3f} {M/sqn:>7.3f} {Cworst:>7} {Cworst/sqn:>10.3f} "
              f"{argmax_eq:>9} {rho:>15.4f}")

if __name__=="__main__":
    main()
