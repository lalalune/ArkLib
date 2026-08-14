#!/usr/bin/env python3
"""
Fisher/pairwise-intersection bound = Johnson boundary, verified for SMOOTH RS (#389, 2026-06-13).

Claim being checked numerically (the wall-unification derivation):
  For RS[F_p, mu_n, k], list codewords pairwise share <= k-1 agreement points (c_i-c_j is a
  nonzero deg<k poly). The Fisher/Jensen double-count then gives the EXACT Johnson bound
      L  <=  (a-k+1)*n / (a^2 - (k-1)*n),      a = (1-delta)*n,
  which is finite iff a > sqrt((k-1)n)  <=>  delta < 1 - sqrt(rho)  (Johnson), and DIVERGES at
  Johnson. Beyond Johnson the bound is vacuous. We confirm:
   (1) below Johnson: actual worst-case structured-word list <= Fisher bound (consistent);
   (2) the Fisher bound -> infinity exactly at the Johnson radius;
   (3) just past Johnson the actual list jumps well above any value the formula gave below.
This shows the elementary pairwise structure yields Johnson and NOTHING beyond -- the smooth
domain does not change the pairwise step; breaking Johnson needs >=3-wise (higher-energy) structure.
"""
import itertools, math

def is_prime(m):
    if m<2: return False
    for i in range(2,int(m**0.5)+1):
        if m%i==0: return False
    return True
def find_prime(n,lo):
    p=max(lo,n+1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        vals=set(); xx=1
        for _ in range(p-1):
            xx=(xx*g0)%p; vals.add(xx)
        if len(vals)==p-1:
            g=pow(g0,(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def list_size(p,H,w,k,a_min):
    n=len(H); found=set()
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]; ys=[w[i] for i in sub]
        if len(set(xs))!=k: continue
        ev=[]
        for j in range(n):
            X=H[j]; fx=0
            for i in range(k):
                num=ys[i]%p; den=1
                for l in range(k):
                    if l==i: continue
                    num=num*((X-xs[l])%p)%p; den=den*((xs[i]-xs[l])%p)%p
                fx=(fx+num*pow(den,p-2,p))%p
            ev.append(fx)
        if sum(1 for j in range(n) if ev[j]==w[j])>=a_min:
            found.add(tuple(ev))
    return len(found)

def fisher_bound(n,k,a):
    denom = a*a - (k-1)*n
    if denom<=0: return math.inf
    return (a-k+1)*n/denom

def run(n,k):
    p=find_prime(n,2*n)
    if p>120: return
    H=subgroup(p,n); rho=k/n
    a_john = math.sqrt((k-1)*n)            # agreement at Johnson (exact pairwise form)
    print(f"\nn={n} k={k} p={p} rho={rho:.3f}  Johnson agreement a*={a_john:.2f} "
          f"(delta_J={1-a_john/n:.3f})")
    # structured worst-word candidates (deep holes)
    cands=[("x^%d"%d,[pow(x,d,p) for x in H]) for d in (k,k+1,n-1)]
    cands.append(("x^k+inv",[(pow(x,k,p)+pow(x,n-1,p))%p for x in H]))
    print("   a   delta  FisherUB   actualMaxList   (worst word)")
    for a in range(k+1, n):
        fb=fisher_bound(n,k,a)
        best=0;bw=None
        for name,w in cands:
            L=list_size(p,H,w,k,a)
            if L>best: best=L;bw=name
        fbs = "inf" if fb==math.inf else f"{fb:8.2f}"
        side = "below-J" if a> a_john else ("AT/above-J" )
        print(f"  {a:3d} {1-a/n:5.3f} {fbs:>9}   {best:4d}   ({bw})  [{side}]")

if __name__=="__main__":
    for (n,k) in [(8,2),(8,3),(8,4),(16,4),(16,6)]:
        run(n,k)
