#!/usr/bin/env python3
"""
P7 v4 (the DECISIVE measurement): isolate the GENUINE mu_n-specific HOMDS excess
corank = (corank on mu_n-coset) - (corank on generic points), over exponent windows
that are DISTINCT mod n (so generic corank = 0 and any drop is purely the
multiplicative structure x^n=1).  This is the real higher-order-MDS gap of mu_{2^mu}.

Question (a): is the mu_n-SPECIFIC excess corank d at constant rate O(1) or growing
with order ell ~ Theta(log n)?

We enumerate exponent multisets E of size a (a = sub-subgroup order 2^j | n) that are
DISTINCT mod n but COLLIDE mod a (the AbacusNCore nonempty a-core condition) -- exactly
the windows where Schur s_lambda(mu_a) vanishes over C while a generic Vandermonde does
NOT.  For each we record the F_p corank (thick p>>n^2) = the structural drop.  We then
track the MAXIMUM structural corank as a function of (a, ell, n) and read the growth law.
"""
import math, itertools, random, json
from collections import Counter

def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def prime_factors(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s
def subgroup(p,n):
    e=(p-1)//n;pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1:continue
        if any(pow(h,n//q,p)==1 for q in pf):continue
        S=[pow(h,j,p) for j in range(n)]
        if len(set(S))==n:return h,S
    raise RuntimeError("no subgroup")
def find_thick_prime(n,blo=2.5,bhi=3.5):
    lo=max(n*2+1,int(n**blo));hi=int(n**bhi);m=max(2,lo//n)
    while n*m+1<=hi:
        p=n*m+1
        if isprime(p):return p
        m+=1
    for mm in range(2,16_000_000//n):
        p=n*mm+1
        if p>16_000_000:break
        if isprime(p):return p
    return None
def matrank_modp(rows,p):
    A=[[x%p for x in r] for r in rows]
    if not A:return 0
    nc=len(A[0]);rank=0;nr=len(A)
    for col in range(nc):
        piv=next((r for r in range(rank,nr) if A[r][col]%p),None)
        if piv is None:continue
        A[rank],A[piv]=A[piv],A[rank]
        inv=pow(A[rank][col],p-2,p)
        A[rank]=[x*inv%p for x in A[rank]]
        for r in range(nr):
            if r!=rank and A[r][col]:
                f=A[r][col]
                A[r]=[(A[r][c]-f*A[rank][c])%p for c in range(nc)]
        rank+=1
        if rank==nr:break
    return rank

def main():
    random.seed(17)
    results={"target":"P7-bgm-rmds-explicit-v4","rows":[]}
    print("="*100)
    print("P7 v4: GENUINE mu_n-specific HOMDS excess corank (exponents DISTINCT mod n) at thick p>>n^2")
    print("       agreement A = sub-subgroup mu_a (a=2^j | n). excess = corank_muA - corank_generic")
    print("="*100)
    print(f"{'n':>3} {'a':>3} {'p':>10} {'#windows(distinct mod n)':>24} {'#with mu_a-drop':>16} "
          f"{'max corank':>11} {'all cg=0?':>10}")
    rows=[]
    growth={}
    for mu in (3,4,5,6):
        n=2**mu
        p=find_thick_prime(n,2.5,3.5)
        if p is None: continue
        w,S=subgroup(p,n)
        genpts=random.sample(range(1,p),n)
        # sub-subgroups mu_a, a=2^j, 2<=a<=n
        for j in range(1,mu+1):
            a=2**j
            step=n//a
            Aidx=[(step*t)%n for t in range(a)]          # mu_a (evenly spaced a-th roots)
            # enumerate exponent windows E (size a): DISTINCT mod n but allowed to collide mod a.
            # to keep feasible, draw exponents from [0, 2n) and require distinct mod n.
            # full enumeration C(2n choose a) too big for large a -> cap by sampling for big a.
            wins=0; drops=0; maxc=0; allcg0=True; examples=[]
            pool=list(range(2*n))
            if math.comb(2*n,a) <= 4000:
                gen = itertools.combinations(pool,a)
            else:
                def sampler():
                    seen=set()
                    for _ in range(4000):
                        c=tuple(sorted(random.sample(pool,a)))
                        if c in seen: continue
                        seen.add(c); yield c
                gen = sampler()
            for E in gen:
                E=list(E)
                if len(set(e%n for e in E))<a:   # require DISTINCT mod n (generic non-vanishing)
                    continue
                wins+=1
                Mg=[[pow(genpts[i],e,p) for e in E] for i in Aidx]
                cg=a-matrank_modp(Mg,p)
                if cg!=0: allcg0=False
                Mm=[[pow(S[i],e,p) for e in E] for i in Aidx]
                cm=a-matrank_modp(Mm,p)
                exc=cm-cg
                if exc>0:
                    drops+=1
                    if cm>maxc:
                        maxc=cm
                        examples=[(E,cm,cg)]
                    elif cm==maxc and len(examples)<3:
                        examples.append((E,cm,cg))
                if wins>=4000: break
            growth.setdefault(n,{})[a]=maxc
            print(f"{n:>3} {a:>3} {p:>10} {wins:>24} {drops:>16} {maxc:>11} {str(allcg0):>10}")
            rows.append(dict(n=n,a=a,p=p,nWindows=wins,nDrops=drops,maxCorank=maxc,
                             allGenericZero=allcg0,examples=[(e,cm,cg) for (e,cm,cg) in examples]))
    results["rows"]=rows
    print("\n"+"="*60)
    print("GROWTH LAW: max mu_n-specific HOMDS excess corank vs (n, a=agreement size)")
    print(f"{'n':>4} | " + " ".join(f"a={2**j:>3}" for j in range(1,7)))
    for n in sorted(growth):
        line=f"{n:>4} | "
        for j in range(1,7):
            a=2**j
            v=growth[n].get(a,"-")
            line+=f"  {str(v):>4}"
        print(line)
    print("\nINTERPRETATION:")
    print(" - excess corank = HOMDS gap of mu_n BEYOND generic (pure x^n=1 structure).")
    print(" - if max corank stays O(1) as n,a grow -> rMDS_d with d=O(1) -> CRACK (list stays generic).")
    print(" - if max corank grows with a (=Theta(a) or Theta(log) of window) -> route CLOSED (= BGK wall).")
    # quantify: is maxc ~ a-1 (full drop), ~log a, or O(1)?
    for n in sorted(growth):
        amax=max(growth[n]); cmax=growth[n][amax]
        print(f"   n={n}: largest a tested={amax}, max excess corank there={cmax}, "
              f"ratio corank/(a-1)={cmax/max(1,amax-1):.3f}")
    with open("P7_homds_excess_corank_results.json","w") as f:
        json.dump(results,f,indent=2,default=str)
    print("[written P7_homds_excess_corank_results.json]")

if __name__=="__main__":
    main()
