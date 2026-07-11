#!/usr/bin/env python3
"""
#407 — Direct test of the LACUNARY FLOOR: compute #lacBad(mu_n, k+t, t) exactly and locate
the crossover #lacBad = B, comparing the resulting delta* to prizeDeltaStar = 1-rho-H/log2(B).

#lacBad(G,a,t) = #{ distinct e_t(S) mod q : S subset of mu_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 }.
(= #bad gamma for the deep-band/monomial direction (X^a, X^k), b=k=a-t, by the proven Vieta pin.)

Verifies: (i) #lacBad is a multiple of n/gcd(t,n) (the proven coset quantization);
(ii) the crossover delta* vs prizeDeltaStar; (iii) whether the floor #lacBad <= C*n holds in the
window (t >= t0) and the small-t (near-capacity) blow-up.
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

def prime_1_mod_n(n, beta):
    lo=int(n**beta); lo+=(1-lo)%n; p=lo
    while True:
        if is_prime(p) and not ((p-1)&(p-2))==0: return p
        p+=n

def order_n_gen(p,n):
    fac=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac): return pow(h,(p-1)//n,p)

def esym(S_vals, t, p):
    """elementary symmetric e_t of a list of field elements, mod p (DP)."""
    e=[0]*(t+1); e[0]=1
    for x in S_vals:
        for j in range(min(t,len(e)-1),0,-1):
            e[j]=(e[j]+e[j-1]*x)%p
    return e[t]

def esym_all(S_vals, tmax, p):
    e=[0]*(tmax+1); e[0]=1
    for x in S_vals:
        for j in range(min(tmax,len(e)-1),0,-1):
            e[j]=(e[j]+e[j-1]*x)%p
    return e  # e[0..tmax]

def Hb(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

print("="*94)
print("LACUNARY FLOOR crossover test:  #lacBad(mu_n,k+t,t) vs budget B,  delta* vs prizeDeltaStar")
print("="*94)
for n, beta in ((16,3.0),(16,4.0),(24,3.0)):
    p=prime_1_mod_n(n,beta); g=order_n_gen(p,n)
    powg=[pow(g,i,p) for i in range(n)]
    for rho in (0.25, 0.5):
        k=int(round(rho*n))
        print(f"\n n={n} q={p} (beta={math.log(p)/math.log(n):.2f}) rho={rho} k={k} | "
              f"Johnson 1-sqrt(rho)={1-rho**0.5:.3f}  cap 1-rho={1-rho:.3f}")
        print(f"   {'t':>2} {'a=k+t':>5} {'delta':>6} | {'#variety':>9} {'#lacBad':>8} {'n/gcd':>6} "
              f"{'mult?':>5} | {'zone':>10}")
        rows=[]
        for t in range(1, n-k+1):
            a=k+t
            if math.comb(n,a) > 4_000_000:  # keep exhaustive feasible
                continue
            gcd=math.gcd(t,n); unit=n//gcd
            img=set(); nvar=0
            for S in itertools.combinations(range(n),a):
                vals=[powg[j] for j in S]
                e=esym_all(vals, t, p)
                if all(e[j]==0 for j in range(1,t)):   # e_1..e_{t-1}=0
                    nvar+=1
                    img.add(e[t])
            nb=len(img)
            mult = (nb % unit == 0) if nb>0 else True
            delta=1-a/n
            J=1-rho**0.5; cap=1-rho
            zone = "<J" if delta<J-1e-9 else ("[J,cap)" if delta<cap-1e-9 else ">=cap")
            print(f"   {t:>2} {a:>5} {delta:>6.3f} | {nvar:>9} {nb:>8} {unit:>6} "
                  f"{str(mult):>5} | {zone:>10}")
            rows.append((t,a,delta,nb,zone))
        # crossover at B=n: largest delta (smallest a / smallest t) with #lacBad<=n
        good=[d for (t,a,d,nb,z) in rows if nb<=n]
        dstar = max(good) if good else None
        B=n; pds = 1-rho - Hb(rho)/math.log2(B) if B>2 else None
        print(f"   -> crossover delta*(B=n) = {dstar}   prizeDeltaStar(B=n)={pds:.3f}" if dstar is not None
              else f"   -> no good delta at B=n")
print()
print("KEY CHECKS: (1) #lacBad always a multiple of n/gcd(t,n) [proven coset quantization];")
print("            (2) small t (near cap) => #lacBad large (ceiling side); large t (window) => small;")
print("            (3) crossover delta* vs prizeDeltaStar.")
