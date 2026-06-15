#!/usr/bin/env python3
"""#407 CRACK 1 reconciliation: the floor in the STRICT prize band (beta=log_n p >= 4 AND m odd).
My 2D coupling probe pooled ALL primes incl. thick beta<4 (driving the positive cross-term).
Crack-audit claims: filtered to beta>=4, m-odd, C=M/sqrt(2n log(p/n)) is bounded <1 with NO n-growth.
Decisive test: does C stay bounded & flat in n in the STRICT band? If yes, floor survives in-regime
and my 2D coupling was a thick-prime artifact."""
import numpy as np
from sympy import isprime
def Mmax(p,n):
    fac=set();x=p-1;d=2
    while d*d<=x:
        while x%d==0:fac.add(d);x//=d
        d+=1
    if x>1:fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac):g+=1
    h=pow(g,(p-1)//n,p);ind=np.zeros(p);cur=1
    for _ in range(n):ind[cur]=1.0;cur=cur*h%p
    F=np.abs(np.fft.rfft(ind));F[0]=-1.0;return F.max()
print("STRICT prize band: beta=log_n(p) >= 4  AND  m=(p-1)/n ODD (v2(p-1)=mu, prize-choosable)")
print(f"{'n':>4} {'#primes':>7} {'beta-range':>14} {'median C':>9} {'worst C':>8} {'C/sqrt2 worst':>13}")
print("-"*64)
summ={}
for n in [16,32,64]:
    mmin = n**3            # p>=n^4 <=> m>=n^3
    Cs=[]; betas=[]
    m = mmin if mmin%2==1 else mmin+1
    pmax = 30_000_000 if n<=64 else 5_000_000
    while len(Cs) < (12 if n<=32 else 6):
        p = n*m+1
        if p>pmax: break
        if isprime(p):    # m odd guaranteed by step
            M=Mmax(p,n); C=M/np.sqrt(2*n*np.log(p/n))
            Cs.append(C); betas.append(np.log(p)/np.log(n))
        m+=2
        if n>=64: m += 2*((n**3)//400)  # sample sparser at large n to span beta
    if not Cs: print(f"{n:>4}  (none in range)"); continue
    Cs=np.array(Cs)
    summ[n]=(np.median(Cs),Cs.max())
    print(f"{n:>4} {len(Cs):>7} {f'{min(betas):.2f}-{max(betas):.2f}':>14} {np.median(Cs):>9.4f} {Cs.max():>8.4f} {Cs.max()/np.sqrt(2):>13.4f}")
print("\nn-trend of worst C:", {n:round(w,3) for n,(med,w) in summ.items()})
print("VERDICT: if worst C stays ~1 (<1.2) and FLAT/non-growing in n in the strict band =>")
print("  floor SURVIVES in prize regime (CRACK 1 confirmed); my 2D coupling was thick-prime-confounded.")
