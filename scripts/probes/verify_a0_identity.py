#!/usr/bin/env python3
"""
ADVERSARIAL re-derivation of A0: T_unsigned = sum_{a,b in Z/p} eta_a eta_b eta_{-a-b}.
Claim: = p^2 * n EXACTLY.

Closed-form derivation (the skeptic's check that this is a TELESCOPE, not structural):
  eta_b = sum_{x in mu_n} e_p(b x).
  T = sum_{a,b} (sum_x e(ax))(sum_y e(by))(sum_z e(-(a+b)z))
    = sum_{x,y,z in mu_n} sum_{a} e(a(x-z)) sum_{b} e(b(y-z))
    = sum_{x,y,z} [p if x=z] [p if y=z]
    = p^2 * #{(x,y,z): x=z, y=z} = p^2 * #{z} = p^2 * n.
So T_unsigned = p^2 * n IDENTICALLY -- depends ONLY on |mu_n|=n, NO subgroup structure. DEAD/telescope.
This is the b->frequency dual of the Parseval/q*E_r wall: it counts the DIAGONAL.

Verify exactly at small n,p with exact complex (sympy-free, integer-index, double ok for small).
"""
import numpy as np
def isprime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
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
def find_prime(n,beta):
    t=int(round(n**beta)); p=t-(t%n)+1
    while p<=t or not isprime(p): p+=n
    return p

# direct O(p^2) double-sum (small p only) using exact-ish complex, compare to p^2 n
for n,beta in [(8,2.0),(8,2.3),(16,2.0),(8,3.0)]:
    p=find_prime(n,beta); S=subgroup(p,n)
    w=np.exp(2j*np.pi/p)
    b=np.arange(p)
    eta=np.zeros(p,dtype=np.complex128)
    for x in S: eta+=w**((b*x)%p)
    # T = sum_{a,b} eta_a eta_b eta_{-(a+b)}
    A,B=np.meshgrid(b,b,indexing='ij')
    idx=(-(A+B))%p
    T=np.real(np.sum(eta[A]*eta[B]*eta[idx]))
    # also the DIRECT combinatorial diagonal count for sanity
    Sset=set(S); diag=sum(1 for z in S)  # #{(x,y,z):x=z,y=z}=n
    print(f"n={n} p={p}: T_unsigned={T:.4f}  p^2*n={p*p*n}  ratio={T/(p*p*n):.8f}  diag_count={diag} (=n)")
