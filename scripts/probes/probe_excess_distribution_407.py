#!/usr/bin/env python3
"""
#407 — Test the AVERAGE-over-q reframing: sweep many primes q and measure the window-edge EXCESS
(= F_q-variety count − char-0 count) of the vanishing-power-sum variety. If MOST q have excess 0/small
and only FEW are bad, the 'pick a good q' route is real (softer than worst-case). If most q are bad,
the average framing fails.

excess_q(t) = #{S⊆μ_n : |S|=a, e_1(S)=…=e_{t-1}(S)=0 in F_q} − #{same, exactly in ℂ (char-0)}.
"""
import itertools, math
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    fs=set();d=2
    while d*d<=m:
        while m%d==0:fs.add(d);m//=d
        d+=1
    if m>1:fs.add(m)
    return fs

def order_n_gen(p,n):
    fac=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac): return pow(h,(p-1)//n,p)
    return None

# char-0 count via exact ℤ[ζ_n] (length-n/2 int vectors, ζ^{n/2}=-1)
def mul_zeta(v,i,half):
    out=[0]*half; n=2*half
    for s in range(half):
        if v[s]:
            m=(s+i)%n
            if m<half: out[m]+=v[s]
            else: out[m-half]-=v[s]
    return out
def char0_count(n, a, t):
    half=n//2; cnt=0
    for S in itertools.combinations(range(n),a):
        e=[[0]*half for _ in range(t)]; e[0][0]=1
        ok=True
        for i in S:
            for j in range(min(t-1,len(e)-1),0,-1):
                term=mul_zeta(e[j-1],i,half)
                for r in range(half): e[j][r]+=term[r]
        for j in range(1,t):
            if any(e[j]): ok=False; break
        if ok: cnt+=1
    return cnt

def fq_count(n,a,t,p,g):
    powg=[pow(g,i,p) for i in range(n)]; cnt=0
    for S in itertools.combinations(range(n),a):
        e=[0]*t; e[0]=1; ok=True
        for i in S:
            xi=powg[i]
            for j in range(min(t-1,t-1),0,-1):
                e[j]=(e[j]+e[j-1]*xi)%p
        for j in range(1,t):
            if e[j]!=0: ok=False; break
        if ok: cnt+=1
    return cnt

print("="*84)
print("EXCESS DISTRIBUTION over q: is the window-edge excess 0 for MOST q? (avg-q reframing test)")
print("="*84)
for n,rho,t in ((8,0.25,2),(8,0.5,2),(16,0.25,2)):
    half=n//2; k=int(round(rho*n)); a=k+t
    c0=char0_count(n,a,t)
    # sweep primes q ≡ 1 mod n in a range ~ n^3..n^4
    lo=int(n**3); hi=int(n**4)
    qs=[]; q=lo+(1-lo)%n
    while q<hi and len(qs)<60:
        if is_prime(q): qs.append(q)
        q+=n
    exc=[]
    for q in qs:
        g=order_n_gen(q,n)
        if g is None: continue
        fc=fq_count(n,a,t,q,g)
        exc.append(fc-c0)
    exc.sort()
    nz=sum(1 for e in exc if e>0)
    print(f"\n n={n} rho={rho} t={t} a={a}: char-0 count={c0}, budget qε*~n={n}")
    print(f"   swept {len(exc)} primes q in [{lo},{hi}]  (excess = F_q count − char-0)")
    print(f"   excess: min={exc[0]} median={exc[len(exc)//2]} max={exc[-1]} mean={sum(exc)/len(exc):.2f}")
    print(f"   #q with excess>0: {nz}/{len(exc)} = {100*nz/len(exc):.0f}%   "
          f"#q with excess>budget({n}): {sum(1 for e in exc if e>n)}/{len(exc)}")
print()
print("If most q have excess 0 (or ≤ budget) and only few exceed: 'pick a good q' route is REAL,")
print("and the residual is an average-over-q (large-sieve) statement, softer than worst-case.")
