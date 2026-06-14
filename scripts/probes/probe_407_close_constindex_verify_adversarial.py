#!/usr/bin/env python3
"""
ADVERSARIAL re-derivation of the constindex-energy claim from scratch.
Independent of the attacker's probe code.

Claims to check:
(C1) Identity: A_k := E_k(mu_n) - n^{2k}/p  ==  (1/p) * sum_{b!=0} |eta_b|^{2k},
     where eta_b = sum_{x in mu_n} e_p(b x),  E_k = sum over k-tuples additive energy moment.
     ACTUALLY: the additive-energy moment E_k(mu_n) := #{(x_1..x_k,y_1..y_k) in mu_n^{2k} :
       x_1+...+x_k = y_1+...+y_k}.  Standard Fourier: E_k = (1/p) sum_b |eta_b|^{2k}.
     So A_k = E_k - (1/p)|eta_0|^{2k} = E_k - n^{2k}/p  (since eta_0 = n).  Check this.
(C2) Structural bound: A_k <= m^{k-1} n^k  where m=(p-1)/n is the index.
(C3) Holder step is tight-valid: A_k <= n * B^{2(k-1)}, B = ((m-1)sqrt(p)+1)/m.
(C4) At prize index m~2^128 the bound degrades to trivial Weil (B->sqrt(p)).
"""
import numpy as np, math
from itertools import product

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    if x%3==0: return x==3
    d=5
    while d*d<=x:
        if x%d==0 or x%(d+2)==0: return False
        d+=6
    return True

def primroot(p):
    if p==2: return 1
    phi=p-1; fs=[]; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.append(m)
    for a in range(2,p):
        if all(pow(a,phi//q,p)!=1 for q in fs): return a
    return None

def subgroup(p,n):
    g=pow(primroot(p),(p-1)//n,p)
    s=set(); x=1
    for _ in range(n):
        s.add(x); x=x*g%p
    assert len(s)==n, (p,n,len(s))
    return sorted(s)

def abs_eta(p,dom):
    ind=np.zeros(p)
    for x in dom: ind[x]=1.0
    return np.abs(np.fft.fft(ind))

def Ek_bruteforce(p, dom, k):
    """Direct additive-energy moment E_k = #{sums of k elements equal} via convolution count.
    cnt[s] = #{(x_1..x_k): sum=s}. E_k = sum_s cnt[s]^2."""
    cnt = np.zeros(p, dtype=np.int64)
    for x in dom: cnt[x]+=1
    res = cnt.copy()
    for _ in range(k-1):
        # convolve res with cnt mod p
        new = np.zeros(p, dtype=np.int64)
        nz = np.nonzero(res)[0]
        for s in nz:
            rs = res[s]
            for x in dom:
                new[(s+x)%p]+=rs
        res = new
    return int(np.sum(res.astype(np.float64)**2))  # sum cnt^2

for (n,want_small) in [(4,True),(8,True),(16,True)]:
    # smallest prime 1 mod n
    p=n+1
    while not isprime(p): p+=n
    dom=subgroup(p,n)
    m=(p-1)//n
    A=abs_eta(p,dom)
    print(f"\n=== n={n}, p={p}, index m={m} ===")
    for k in [2,3]:
        Ek_bf = Ek_bruteforce(p,dom,k)
        Ek_fft = float(np.sum(A.astype(np.float64)**(2*k)))/p
        Ak_def = Ek_bf - (n**(2*k))/p
        Ak_tail = float(np.sum(A[1:].astype(np.float64)**(2*k)))/p
        B = ((m-1)*math.sqrt(p)+1)/m
        struct = m**(k-1)*n**k
        holder = n*B**(2*(k-1))
        print(f" k={k}: E_k bf={Ek_bf}  E_k via fft={Ek_fft:.4f}  (match={abs(Ek_bf-Ek_fft)<1e-3})")
        print(f"       A_k(def=E_k-n^2k/p)={Ak_def:.6f}  A_k(tail (1/p)sum_b!=0)={Ak_tail:.6f}  (C1 match={abs(Ak_def-Ak_tail)<1e-3})")
        print(f"       struct bound m^(k-1)n^k={struct}  holder n*B^2(k-1)={holder:.3f}  A_k<=struct? {Ak_def<=struct+1e-6}  A_k<=holder? {Ak_def<=holder+1e-6}")
