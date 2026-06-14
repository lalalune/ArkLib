#!/usr/bin/env python3
import itertools, sys
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
def prime_1_mod_n(n, lo):
    p=(lo|1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=2
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
        if cnt>best:
            best=cnt
            if best==n: break
    return best
def bad_gammas(H, base, fvals, p, k, thr):
    bad=set()
    for g in range(1,p):
        vals=[(base[i]+g*fvals[i])%p for i in range(len(H))]
        if best_agreement(H,vals,p,k)>=thr: bad.add(g)
    return bad
def orbit_closed(badset, mult, p):
    for g in badset:
        if (g*mult)%p not in badset: return False
    return True
def norbits(badset, mult, p):
    seen=set(); K=0
    for g in badset:
        if g in seen: continue
        K+=1; cur=g
        while cur not in seen:
            seen.add(cur); cur=(cur*mult)%p
    return K

def run(n,k,p):
    w=find_gen(p,n); H=[pow(w,i,p) for i in range(n)]
    rho=k/n; dJ=1-sqrt(rho)
    a=n-1; base=[pow(x,a,p) for x in H]
    print(f"\n--- n={n} k={k} rho={rho:.3f} p={p} (proper mu_{n}) Johnson dJ={dJ:.3f} base=x^{a} ---", flush=True)
    dirs=[("MONO x^{}".format(k), [(k,1)]),
          ("GEN  x^{}+x^{}".format(k,k+1), [(k,1),(k+1,1)]),
          ("GEN  x^{}+3x^{}".format(k,(k+2)%n), [(k,1),((k+2)%n,3)])]
    for desc,fexps in dirs:
        fvals=[sum(c*pow(x,e,p) for (e,c) in fexps)%p for x in H]
        print(f"  dir f={desc}:", flush=True)
        for t in range(k+1, n+1):
            d=1-t/n
            bad=bad_gammas(H, base, fvals, p, k, t)
            reg="INT" if d>dJ+1e-9 else "J/blw"
            # find best nontrivial dilation closure
            best_j=None; best_K=10**9
            for j in range(1,n):
                m=pow(w,j,p)
                if m==1: continue
                if orbit_closed(bad,m,p):
                    K=norbits(bad,m,p)
                    if K<best_K: best_K=K; best_j=j
            if best_j is not None:
                print(f"    t={t} d={d:.3f}[{reg:5}] |bad|={len(bad):4d}  closed@w^{best_j} #orb={best_K} (n*K={n*best_K})", flush=True)
            else:
                print(f"    t={t} d={d:.3f}[{reg:5}] |bad|={len(bad):4d}  NO dilation closure", flush=True)

run(8,2,prime_1_mod_n(8,400))
run(8,3,prime_1_mod_n(8,400))
run(8,4,prime_1_mod_n(8,400))
print("\nDONE", flush=True)
