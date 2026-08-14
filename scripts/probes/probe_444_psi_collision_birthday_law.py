#!/usr/bin/env python3
"""DECISIVE TEST: is #distinct(F_p r-sums) governed PURELY by birthday on N_r balls into p bins,
or is there ARITHMETIC structure (deviation from the random-collision prediction)?
Random model: E[#distinct] = p*(1-(1-1/p)^N_r) for N_r 'balls' uniform into p bins.
We FULL-ENUMERATE at n=32, r=4 (C(32,4)=35960 manageable) across betas where N_r/p crosses 1,
and compare actual #distinct vs the birthday prediction with N=C(n,r) trials (NOT N_r --
the relevant ball count is the number of SUBSETS C(n,r), each landing in some residue)."""
import math
from itertools import combinations

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def find_prime(n,beta):
    target=int(n**beta); k0=max(2,target//n)
    for dk in range(60000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n and isprime(p):
                if ((p-1)//n)%2==1: return p
    return None
def subgroup(n,p):
    def pr(g):
        x=p-1; fs=set(); d=2
        while d*d<=x:
            while x%d==0: fs.add(d); x//=d
            d+=1
        if x>1: fs.add(x)
        return all(pow(g,(p-1)//q,p)!=1 for q in fs)
    g=2
    while not pr(g): g+=1
    h=pow(g,(p-1)//n,p); S=[]; c=1
    for _ in range(n): S.append(c); c=c*h%p
    return S
def Nr_cf(n,r):
    m=n//2; tot=0; k=r%2; kmax=min(r,2*m-r)
    while k<=kmax:
        if k<=m: tot+=math.comb(m,k)*2**k
        k+=2
    return tot

n=32; r=4
Nr=Nr_cf(n,r)
Csub=math.comb(n,r)
print(f"n={n} r={r}: char-0 N_r={Nr}, #subsets C(n,r)={Csub}")
print(f"{'beta':>5} {'p':>12} {'N_r/p':>9} {'#distinct':>10} {'birthday_pred':>13} {'actual/pred':>11} {'dist/min(Nr,p)':>14}")
for beta in [2.0,2.3,2.6,3.0,3.5,4.0]:
    p=find_prime(n,beta)
    if p is None: continue
    S=subgroup(n,p)
    seen=set()
    for comb in combinations(S,r):
        seen.add(sum(comb)%p)
    d=len(seen)
    # birthday: Csub subsets, but they realize only Nr distinct char-0 values; each char-0 value
    # maps to a residue. So #distinct mod p = #distinct residues among Nr char-0 values.
    # model Nr values uniform into p bins: E = p*(1-(1-1/p)**Nr)
    pred = p*(1-(1-1/p)**Nr)
    cap = min(Nr,p)
    print(f"{beta:>5} {p:>12} {Nr/p:>9.3f} {d:>10} {pred:>13.1f} {d/pred:>11.4f} {d/cap:>14.4f}")
