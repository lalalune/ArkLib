#!/usr/bin/env python3
"""
#407 — REFUTATION TEST: is delta* = prizeDeltaStar ROBUST, or does the WORST-CASE code (adversarial
prime / relation-rich, e.g. Fermat) push delta* strictly BELOW prizeDeltaStar?

If worst-case delta* < prizeDeltaStar, then prizeDeltaStar is NOT the worst-case answer, and the
true worst-case delta* (which would then be the honest closed target) is lower. If delta* is
robust (= the same staircase regardless of prime), prizeDeltaStar survives the refutation.

We compute the EXACT incidence #lacBad(μ_n, k+t, t) = #distinct e_t(S) over {|S|=k+t, e_1..e_{t-1}=0}
(the bad-scalar count) and locate the crossover delta*(B=n), for:
  (a) relation-free generic primes (q ~ n^3, non-Fermat),
  (b) ADVERSARIAL primes: Fermat (q-1 a pure 2-power), and small-multiplicative-order primes.
Compare crossover delta* across primes at fixed n.
"""
import itertools, math
from collections import defaultdict

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
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

def esym_all(vals, tmax, p):
    e=[0]*(tmax+1); e[0]=1
    for x in vals:
        for j in range(min(tmax,len(e)-1),0,-1):
            e[j]=(e[j]+e[j-1]*x)%p
    return e

def Hb(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

def crossover(n, p, rho):
    g=order_n_gen(p,n); powg=[pow(g,j,p) for j in range(n)]
    k=int(round(rho*n))
    rows=[]
    for t in range(1, n-k+1):
        a=k+t
        if math.comb(n,a) > 2_500_000: continue
        img=set()
        for S in itertools.combinations(range(n),a):
            e=esym_all([powg[j] for j in S], t, p)
            if all(e[j]==0 for j in range(1,t)):
                img.add(e[t])
        rows.append((t,a,1-a/n,len(img)))
    good=[d for (t,a,d,nb) in rows if nb<=n]
    return (max(good) if good else None), rows

print("="*80)
print("REFUTATION: worst-case delta* across primes (relation-free vs adversarial/Fermat)")
print("="*80)
for n in (16,):
    half=n//2
    # generic relation-free primes (~n^3), avoid Fermat
    gen=[]
    p=int(n**3); p+=(1-p)%n
    while len(gen)<3:
        if is_prime(p) and not ((p-1)&(p-2))==0: gen.append(p)
        p+=n
    # adversarial: Fermat 65537 (n=16: 65537-1=65536=2^16, pure 2-power) + a few 2-power-heavy
    adv=[]
    if n==16:
        adv=[65537]  # Fermat: q-1 = 2^16 (maximally 2-adic) — the #400 trap
        # also 2-power-heavy: q-1 = 2^a * small
        p=int(n**3)
        while len(adv)<3:
            if is_prime(p) and ((p-1)>>(((p-1)&-(p-1)).bit_length()-1)) <= 8:  # large 2-adic valuation
                adv.append(p)
            p+=n
    for rho,rl in ((0.25,"1/4"),(0.5,"1/2")):
        k=int(round(rho*n))
        B=n; pds=1-rho - Hb(rho)/math.log2(B)
        J=1-rho**0.5; cap=1-rho
        print(f"\n n={n} rho={rl} k={k} | Johnson={J:.3f} prizeDeltaStar={pds:.3f} cap={cap:.3f}")
        print(f"   {'prime':>8} {'type':>12} {'2-adic(q-1)':>11} | {'crossover δ*':>12} {'vs pDS':>8}")
        for p in gen:
            ds,_=crossover(n,p,rho)
            v2=((p-1)&-(p-1)).bit_length()-1
            flag = "=" if ds is not None and abs(ds-pds)<1.5/n else ("<pDS!" if ds is not None and ds<pds else ">pDS")
            print(f"   {p:>8} {'relation-free':>12} {v2:>11} | {str(ds):>12} {flag:>8}")
        for p in adv:
            ds,_=crossover(n,p,rho)
            v2=((p-1)&-(p-1)).bit_length()-1
            flag = "=" if ds is not None and abs(ds-pds)<1.5/n else ("<pDS!" if ds is not None and ds<pds else ">pDS")
            print(f"   {p:>8} {'ADVERSARIAL':>12} {v2:>11} | {str(ds):>12} {flag:>8}")
print()
print("VERDICT: if adversarial crossover δ* < prizeDeltaStar (flag '<pDS!'), prizeDeltaStar is NOT")
print("the worst-case answer. If all '=' (within staircase 1/n), prizeDeltaStar survives refutation.")
