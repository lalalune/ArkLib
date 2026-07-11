#!/usr/bin/env python3
"""
probe_444r2_z3_thingate.py (#444) -- RULE-3 gate on the zero-sum-triple count Z3(mu_n) and the
absolute-cube moment, across THIN (beta=4,5) vs THICK (beta=2.3,2.6,3.0) primes and MULTIPLE
primes per beta. Question: is Z3=0 (no zero-sum triples => S3 = -n^3 trivially) a THIN-ESSENTIAL
fact, or does it persist thick (=> NOT thin-essential, the cube is structurally trivial everywhere)?

Z3 = #{(x,y,z) in mu_n^3 : x+y+z=0 mod p}.  If Z3=0 always-reachable, then sum_b eta_b^3 = -n^3
EXACTLY (the only zero-sum triple contributions vanish), so the SIGNED cube carries NO subgroup
info beyond Z3 -- it cannot certify M.  We measure Z3 over a grid and also the absolute 3rd moment.
This is exact integer arithmetic (no FFT) -- scales to large n.
"""
import sys
def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
def prime_factors(n):
    s=set(); d=2
    while d*d<=n:
        while n%d==0: s.add(d); n//=d
        d+=1
    if n>1: s.add(n)
    return s
def subgroup(p,n):
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): x=x*h%p; S.append(x)
        if len(set(S))==n: return sorted(S)
    raise RuntimeError
def primes_near(n, beta, count):
    t=int(round(n**beta)); p=t-(t%n)+1; out=[]
    while len(out)<count:
        if p>1 and isprime(p): out.append(p)
        p+=n
    return out
def Z3(p,n,S):
    Sset=set(S); z=0
    for x in S:
        for y in S:
            if (-(x+y))%p in Sset: z+=1
    return z
def Z3_distinct(p,n,S):
    # exclude x=y, etc. -- genuinely distinct zero-sum triples
    Sset=set(S); z=0
    for i,x in enumerate(S):
        for j,y in enumerate(S):
            zz=(-(x+y))%p
            if zz in Sset and zz!=x and zz!=y and x!=y: z+=1
    return z
if __name__=="__main__":
    print("RULE-3 gate on Z3 (zero-sum ordered triples in mu_n) and Z3_distinct.")
    print("If Z3=0 thick too => the SIGNED cube sum_b eta_b^3 = -n^3 carries no info (DEAD), NOT thin-essential.\n")
    for n in [8,16,32,64,128,256]:
        print(f"n={n}:")
        for beta in [2.3,2.6,3.0,4.0,5.0]:
            try:
                ps=primes_near(n,beta,3)
            except Exception as e:
                print(f"  beta={beta}: ERR {e}"); continue
            row=[]
            for p in ps:
                try:
                    S=subgroup(p,n)
                except Exception:
                    row.append((p,'noSub')); continue
                z=Z3(p,n,S); zd=Z3_distinct(p,n,S)
                # correlation gate: skip if X^{n/2}=-1 trivially correlated? that's automatic for 4|n; we note neg-closed
                neg1 = ((-1)%p) in set(S)
                row.append((p,z,zd,neg1))
            print(f"  beta={beta}: " + "  ".join(
                f"p={r[0]} Z3={r[1]} Z3dist={r[2]} (-1in:{r[3]})" if len(r)==4 else f"p={r[0]}:{r[1]}" for r in row))
        print()
