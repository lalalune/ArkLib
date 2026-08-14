#!/usr/bin/env python3
"""
Door-IV Lane 1 PROBE v2 (high-power) — worst-b coset-index QR / d-th-power-residue rate, MANY primes.

v1 was underpowered (2-13 primes/cell). This version collects the ROBUST multiplicative statistic
(quadratic-residue rate of the worst-b coset index I=argmax|S| modulo the largest prime factor of
m=(p-1)/n) over MANY structured primes per n, with a binomial significance check. A real
multiplicative thinness of the worst-b would show QR-rate != 0.5 beyond noise; generic => 0.5.

Honest: |S| is sampled over a prefix of the coset transversal (cap), so I=argmax is the SAMPLED
argmax (lower-bound proxy for true worst-b). The QR statistic of the sampled argmax still tests
whether the (sampled) extremal coset index carries multiplicative structure. PROPER mu_n; p>>n^3;
many structured primes; never n=q-1.
"""
import math
from collections import Counter

def is_prime(p):
    if p<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if p%q==0: return p==q
    d=p-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%p==0: continue
        x=pow(a,d,p)
        if x==1 or x==p-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%p
            if x==p-1: ok=True;break
        if not ok: return False
    return True

def find_primes(n,count,beta=4):
    out=[];k=(n**beta)//n+1
    while len(out)<count:
        p=k*n+1
        if is_prime(p): out.append(p)
        k+=1
    return out

def primitive_root(p):
    phi=p-1;factors=set();m=phi;f=2
    while f*f<=m:
        if m%f==0:
            factors.add(f)
            while m%f==0: m//=f
        f+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors): return g
    raise RuntimeError

def largest_prime_factor(x):
    f=2;lp=1
    while f*f<=x:
        while x%f==0: lp=f; x//=f
        f+=1
    if x>1: lp=x
    return lp

def worstb_index(n,p,cap):
    g0=primitive_root(p)
    g=pow(g0,(p-1)//n,p)
    elems=[1]
    for _ in range(n-1): elems.append(elems[-1]*g%p)
    tp=2*math.pi/p
    cos=math.cos; sin=math.sin
    m=(p-1)//n
    cap=min(m,cap)
    best=-1.0; bestI=0
    b=1
    for t in range(cap):
        re=0.0; im=0.0
        for x in elems:
            a=tp*((b*x)%p)
            re+=cos(a); im+=sin(a)
        A=re*re+im*im
        if A>best: best=A; bestI=t
        b=b*g0%p
    return bestI,m

def main():
    print("# Door-IV worst-b coset-index multiplicative QR-rate (HIGH-POWER, many primes)")
    print("# QR-rate = fraction of worst-b coset indices I that are quadratic residues mod lpf(m).")
    print("# generic = 0.5; |rate-0.5| beyond ~2*se(=sqrt(0.25/N)) would indicate multiplicative thinness.")
    print()
    for n,nprimes,cap in ((16,300,2000),(32,300,2500),(64,200,3000)):
        primes=find_primes(n,nprimes,beta=4)
        qr=0;tot=0
        for p in primes:
            I,m=worstb_index(n,p,cap)
            lp=largest_prime_factor(m)
            if lp<3 or I%lp==0: continue
            tot+=1
            if pow(I%lp,(lp-1)//2,lp)==1: qr+=1
        if tot:
            rate=qr/tot; se=math.sqrt(0.25/tot); z=(rate-0.5)/se
            verdict="GENERIC (consistent with 0.5)" if abs(z)<2 else "BIASED (|z|>=2 — investigate)"
            print(f"n={n}: QR-rate of worst-b coset index = {qr}/{tot} = {rate:.4f}  se={se:.4f}  z={z:+.2f}  => {verdict}")
        print()

if __name__=="__main__":
    main()
