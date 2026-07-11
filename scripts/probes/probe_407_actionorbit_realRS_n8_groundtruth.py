#!/usr/bin/env python3
"""
#407 LANE D -- GROUND-TRUTH the orbit count on GENUINE RS agreement (n=8, full alpha-sweep).

The K-growth-law probe used the gap-variety proxy (alpha = e_m(S), the Kambire value family).
Here we confirm, on ACTUAL Reed-Solomon agreement over mu_8 in F_p (full sweep over all
alpha in F_p, exact deg<k agreement via Lagrange), that:
  (i)  badSet_orbit_closed holds: BAD is exactly a union of <w^{b-a}>-orbits, each of size
       S = n/gcd(b-a,n);
  (ii) the orbit count K = |BAD|/S, i.e. the action compresses by EXACTLY S = the orbit size,
       and NO MORE -- so K tracks L/S, inheriting L's growth (the BGK-collapse mechanism).
n=8 keeps the full F_p sweep feasible. We sweep delta from Johnson into the interior.
"""

import itertools
from math import gcd, sqrt
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

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
        if cnt>best: best=cnt
        if best==n: break
    return best

def analyze(p,n,k,a,b,t):
    w=find_gen(p,n); H=[pow(w,i,p) for i in range(n)]
    Ha=[pow(x,a,p) for x in H]; Hb=[pow(x,b,p) for x in H]
    mult=pow(w,(b-a)%n,p)
    d=(b-a)%n
    S=n//gcd(d if d else n,n)
    BAD=set()
    for alpha in range(1,p):   # exclude alpha=0 (pure monomial, degenerate)
        vals=[(Ha[i]+alpha*Hb[i])%p for i in range(n)]
        if best_agreement(H,vals,p,k)>=t: BAD.add(alpha)
    # orbit-closure check + orbit count
    closed=True
    for alpha in BAD:
        if (alpha*mult)%p not in BAD: closed=False
    seen=set(); K=0; sizes=[]
    for alpha in BAD:
        if alpha in seen: continue
        K+=1; cur=alpha; sz=0
        while cur not in seen:
            seen.add(cur); cur=(cur*mult)%p; sz+=1
        sizes.append(sz)
    return len(BAD), S, K, closed, Counter(sizes)

def main():
    print("="*80)
    print("#407 LANE D -- GENUINE RS agreement, n=8, full F_p sweep.  K vs L=|BAD|.")
    print("="*80)
    for (n,k,p) in [(8,2,401),(8,4,401),(8,2,769),(8,4,769)]:
        rho=k/n; dJ=1-sqrt(rho)
        # far pencil: a,b>=k, b-a != 0, n/2
        a=b=None
        for aa in range(k,n):
            for bb in range(k,n):
                if aa==bb: continue
                dd=(bb-aa)%n
                if dd==0 or dd==n//2: continue
                a,b=aa,bb; break
            if a is not None: break
        print(f"\n--- n={n} k={k} rho={rho:.2f} p={p} pencil(z^{a}+a*z^{b}) Johnson dJ={dJ:.3f} ---")
        print(f"  {'delta':>7} {'t':>3} {'L=|BAD|':>8} {'S':>3} {'K':>4} {'orbit-closed':>12} {'L/S':>6} {'sizes':>14}")
        for t in range(k+1, n+1):
            delta=1-t/n
            L,S,K,closed,szc=analyze(p,n,k,a,b,t)
            reg = "INT" if delta>dJ+1e-9 else "J/below"
            chk = "YES" if closed else "NO!!"
            print(f"  {delta:7.3f} {t:3d} {L:8d} {S:3d} {K:4d} {chk:>12} {(L/S if S else 0):6.1f} {str(dict(szc)):>14}  [{reg}]")

if __name__=="__main__":
    main()
