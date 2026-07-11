#!/usr/bin/env python3
"""C38 follow-up: is B a multiplicative coset union (=> FactorizationRigidity/L3 cap),
and does small mult-energy/BSG bound |B| or is the cardinality the OPEN object?
Tests at moderate, NON-degenerate radii (delta in (J, 1-rho)), proper mu_n, p>>n^3."""
import math, itertools
from collections import Counter

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
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

def find_prize_prime(n,beta):
    target=int(round(n**beta));t=max(2,target//n)
    while True:
        p=1+t*n
        if p>target and isprime(p) and (p-1)//n>=2:return p
        t+=1

def subgroup(p,n):
    g=2
    while not (pow(g,p-1,p)==1 and all(pow(g,(p-1)//q,p)!=1 for q in prime_factors(p-1))):
        g+=1
    h=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*h%p
    assert len(set(S))==n
    return S,h

def bad_set_fast(p,S,k,a,b,delta):
    n=len(S);need=math.ceil((1.0-delta)*n)
    A=[pow(S[i],a,p) for i in range(n)];Bm=[pow(S[i],b,p) for i in range(n)]
    inv=lambda z:pow(z%p,p-2,p);bad=set();allbad=False
    for T in itertools.combinations(range(n),k):
        Tset=set(T);PA=[0]*n;PB=[0]*n
        for j in range(n):
            sa=0;sb=0
            for i in T:
                num=1;den=1
                for ii in T:
                    if ii==i:continue
                    num=num*((S[j]-S[ii])%p)%p;den=den*((S[i]-S[ii])%p)%p
                L=num*inv(den)%p;sa=(sa+L*A[i])%p;sb=(sb+L*Bm[i])%p
            PA[j]=sa;PB[j]=sb
        universal=0;crit=Counter()
        for j in range(n):
            c1=(Bm[j]-PB[j])%p;c0=(PA[j]-A[j])%p
            if j in Tset:universal+=1;continue
            if c1==0:
                if c0==0:universal+=1
            else:crit[(c0*inv(c1))%p]+=1
        if universal>=need:allbad=True
        for al,ex in crit.items():
            if al!=0 and universal+ex>=need:bad.add(al)
    return("ALL",need) if allbad else (sorted(bad),need)

def is_coset_union(B,h,n,p):
    """Check if B is a union of cosets of mu_n (or a subgroup of it). mu_n=<h>.
    A coset of the subgroup gen by h^d (order n/d) is the relevant structure for L3.
    We test: for each divisor d|n, is B a union of cosets of the order-(n/d) subgroup?"""
    Bset=set(B)
    results={}
    for d in range(1,n+1):
        if n%d!=0:continue
        m=n//d  # subgroup <h^d> has order m
        Hg=set();x=1;hd=pow(h,d,p)
        for _ in range(m):Hg.add(x);x=x*hd%p
        # partition B by cosets of Hg: B union of cosets iff for every b in B, b*Hg subset B
        ok=all(all((bb*g)%p in Bset for g in Hg) for bb in Bset)
        if ok and m>1:results[m]=True
    return results

def main():
    print("="*88)
    print("C38 FOLLOW-UP: coset structure of B, energy regime, and the |B| bound direction")
    print("="*88)
    print(f"{'n':>3}{'k':>3}{'rho':>6}{'p':>9}{'(a,b)':>9}{'g(b-a,n)':>9}{'del':>6}{'J':>6}"
          f"{'cap':>6}{'|B|':>5}{'budget':>7}{'>bud?':>6}{'>J?':>5}{'Emult':>8}{'|BB|':>6}{'coset?':>14}")
    for n,k,beta in [(8,2,4.0),(8,2,4.5),(16,2,4.0),(16,4,4.0),(16,2,5.0)]:
        rho=k/n;p=find_prize_prime(n,beta);S,h=subgroup(p,n)
        J=1-math.sqrt(rho);cap=1-rho
        a,b=(k+1)%n,(k+2)%n
        if a==b:a,b=k+1,k+3
        g_ba=math.gcd((b-a)%n,n)
        budget=n  # q*eps* ~ n (the prize budget in incidence units)
        for frac,tag in [(0.55,"pastJ"),(0.85,"nearCap")]:
            delta=J+frac*(cap-J)
            if delta>=cap:continue
            try:
                res,need=bad_set_fast(p,S,k,a,b,delta)
            except Exception as e:
                print(f"  skip n={n}:{e}");continue
            if res=="ALL":
                print(f"{n:>3}{k:>3}{rho:>6.3f}{p:>9}{str((a,b)):>9}{g_ba:>9}{delta:>6.3f}"
                      f"{J:>6.3f}{cap:>6.3f}  ALL-bad(deg);need={need}");continue
            B=res;bl=len(B);E=0;BB=0
            if bl:
                c=Counter()
                for x in B:
                    for y in B:c[(x*y)%p]+=1
                E=sum(v*v for v in c.values());BB=len(c)
            cos=is_coset_union(B,h,n,p) if bl else {}
            coskey=max(cos.keys()) if cos else 0
            print(f"{n:>3}{k:>3}{rho:>6.3f}{p:>9}{str((a,b)):>9}{g_ba:>9}{delta:>6.3f}"
                  f"{J:>6.3f}{cap:>6.3f}{bl:>5}{budget:>7}"
                  f"{('Y' if bl>budget else 'n'):>6}"
                  f"{('Y' if delta>J else 'n'):>5}{E:>8}{BB:>6}"
                  f"{('coset|H|='+str(coskey)) if coskey else 'no':>14}")
    print()
    print("KEY: if B is a coset union (coset?=Y) then |B|=(#cosets)*|coset|, and |B.B|<=|B|")
    print("(coset products stay in finitely many cosets) -- B's mult energy is MAXIMAL (coset =")
    print("perfect mult structure), NOT small. C38's 'small mult energy' premise is then FALSE,")
    print("AND coset closure caps |B| at the L3 orbit count gcd(b-a,n)*(#cosets) -- a JOHNSON object.")

main()
