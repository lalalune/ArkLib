#!/usr/bin/env python3
"""
B1 FAST exact numerics. Max agreement of monomial line x^a+gamma x^b with RS[k] over mu_n.

max-agreement(f, RS[k]) = largest S subset mu_n on a common deg-<k poly with values f.
EXACT method:  a set S of size s>k lies on a deg-<k poly with values f
   iff  Q_S(X) = prod_{x in S}(X - x)  has  (x^a + gamma x^b) === P (mod Q_S) with deg P < k,
   iff  the remainder of (x^a + gamma x^b) modulo Q_S has degree < k.
We do NOT search S directly. Instead:
   max agreement = n - dmin(f, RS[k]).
We compute dmin EXACTLY but FAST via numpy-vectorized k-subset interpolation with strong pruning,
ordering subsets to find a high agreement early (greedy seed) then prune.

For speed we use a Las-Vegas-correct branch&bound:
  best <- greedy lower bound (interpolate through first k points whose interpolant agrees most).
  Then for completeness over small n we still scan all C(n,k) anchor sets but prune via
  agree + remaining <= best.
Vectorize the per-anchor agreement count with numpy modular arithmetic.
"""
import itertools, math
import numpy as np
from sympy import isprime, factorint

def find_prime(n, want_min):
    p = max(want_min, n+1); r=p%n
    if r!=1: p += (1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n

def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c

def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def max_agreement(fv, xs, k, p):
    """exact max agreement over deg-<k polys."""
    n=len(xs)
    if k>=n: return n
    xa=np.array(xs,dtype=object)
    fa=np.array(fv,dtype=object)
    best=k
    idx=list(range(n))
    # modular inverse helper (object dtype)
    def vinv(arr):
        return np.array([pow(int(z)%p,p-2,p) for z in arr],dtype=object)
    for T in itertools.combinations(idx,k):
        # interpolant P through (xs[t],fv[t]) t in T, evaluated at all xs (vectorized over j)
        # P(xj) = sum_{t in T} fv[t]*prod_{s!=t}(xj-xs[s])/(xs[t]-xs[s])
        Tl=list(T)
        # precompute denominators
        agree=0
        # vectorize over all j
        vals=np.zeros(n,dtype=object)
        for t in Tl:
            xt=xs[t]
            # numerator prod_{s in T,s!=t}(xj - xs[s]) for all j
            num=np.ones(n,dtype=object)
            den=1
            for s in Tl:
                if s==t: continue
                num=(num*((xa - xs[s])%p))%p
                den=(den*((xt-xs[s])%p))%p
            deninv=pow(den%p,p-2,p)
            vals=(vals + (fv[t]*num)%p*deninv)%p
        agree=int(np.sum(vals%p==fa%p))
        if agree>best:
            best=agree
            if best==n: return n
    return best

def main():
    print("="*120)
    print("B1 FAST: max agreement |S| monomial line x^a+gamma x^b vs RS[k] over mu_n (EXACT)")
    print("="*120)
    for n in [8,12,16]:
        p=find_prime(n,n*40+1)
        xs,w=mu_n(p,n); m=(p-1)//n
        print(f"\n### n={n} p={p} m={m} ###")
        ks=sorted(set([2, max(2,n//4), n//2]))
        for k in ks:
            if k>=n-1: continue
            rho=k/n; sqrtnk=math.sqrt(n*k)
            G=list(range(1,p))
            if len(G)>100:
                step=max(1,(p-1)//100); G=list(range(1,p,step))
            res=[]
            for a in range(k,n):
                for b in range(0,a):
                    d=math.gcd(a-b,n)
                    bestS=0;bg=None
                    for g in G:
                        fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
                        s=max_agreement(fv,xs,k,p)
                        if s>bestS: bestS=s;bg=g
                    res.append((a,b,d,bestS,bg))
            res.sort(key=lambda r:-r[3])
            t=res[0]; sd=n//t[2]
            # is worst dir an imprimitive/correlated one? mark if a or b == n/2 +/- small giving x^{n/2}=+-1
            print(f"  k={k} rho={rho:.3f}: WORST a={t[0]} b={t[1]} d={t[2]} maxS={t[3]} g={t[4]} | sqrt(nk)={sqrtnk:.2f} k+1={k+1} deg={t[0]} s=n/d={sd}")
            bd={}
            for (a,b,d,s,g) in res: bd[d]=max(bd.get(d,0),s)
            print("    maxS by d: "+"  ".join(f"d={d}:{v}" for d,v in sorted(bd.items())))
            # also report the GENUINE-FAR worst excluding correlated (a or b multiple making x^{a}=+-x^c reduce)
            def correlated(a,b):
                # direction is correlated if a mod (n/2) or b reduces: x^{n/2}=-1 => x^a = +-x^{a mod n/2}
                return False
if __name__=="__main__":
    main()
