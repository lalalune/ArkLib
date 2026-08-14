#!/usr/bin/env python3
"""
#407 C5 — adversarial: pin the BGK CROSSOVER and the k=1 "Parseval" claim.

The task warns: the #1 failure is a connection that folds back to the BGK deep-moment wall
(the r*~beta+1 crossover) where char-p energy A_k EXCEEDS char-0 Wick (2k-1)!! n^k.

(B1) Confirm the crossover: as a function of k (=r), find where A_k(n)/Wick crosses 1.
     The recursion's "per-level ratio in (2^k, 4^k]" is exactly the statement that A_k is NOT
     pinned at Wick. Show: the level where A_k/Wick > 1 is the SAME char-p anomaly the prize needs
     to control at r~ln q. So the recursion's interior+twist obstruction = exactly the A_k>Wick excess.

(B2) k=1 closure: the agent says A_1(n)/A_1(n/2)->2 IS "the proven E_2(mu_n)=3n^2-3n pairwise indep".
     Check: A_1(n) = (1/p)sum_{b!=0}|eta_b|^2. By Parseval sum_b|eta_b|^2 = p*n (NOT energy!).
     So A_1(n) = n - n^2/p  -- this is the SECOND moment = E_1 energy = n, TRIVIAL (Parseval),
     it has NOTHING to do with E_2=3n^2-3n (which is the 4th moment = A_2). VERIFY the agent
     MISLABELED which energy closes k=1. (If so, k=1 closes by TRIVIAL Parseval, even weaker claim.)
     The genuine E_2(mu_n) = sum over 2nd additive energy = A_2-related. Check E_2(mu_n) value.

(B3) The decisive circularity statement: A_k(n) <= Wick FOR ALL k <= ~ln q  IS the prize
     (gives M(n)<=sqrt(2n ln q) by union/min-over-r). The recursion expresses A_k(n) via
     A_k(n/2)+interior-twist. Does ANY finite stage of the recursion bound A_k(n) by char-0
     Wick WITHOUT already assuming A_k(n/2) <= Wick (i.e. the same statement one level down)?
     -> if the only telescoping uses Young (ratio 4^k = trivial), and Wick-per-level (2^k) is
     UNPROVEN, then the recursion ASSUMES the open lemma at the base or needs it at every level.
"""
import numpy as np
from sympy import isprime, primitive_root as pr
from math import comb

def eta_all(n,p):
    g=int(pr(p)); t=pow(g,(p-1)//n,p)
    ind=np.zeros(p); x=1
    for _ in range(n): ind[x]+=1.0; x=(x*t)%p
    return np.conjugate(np.fft.fft(ind))

def dfact(m):
    r=1
    for j in range(1,m+1,2): r*=j
    return r

def main():
    print("="*100)
    print("(B1) BGK CROSSOVER: smallest k where A_k(n) > Wick=(2k-1)!! n^k  (char-p anomaly onset).")
    print("     beta := log_2(p/n) roughly. Crossover r* claim ~ beta+1.")
    print("="*100)
    for n in [8,16,32,64]:
        # pick a prize-ish prime p ~ n^? sweep a few
        for tgt in [n*n, n*n*n]:
            p=tgt
            while not (isprime(p) and (p-1)%n==0): p+=1
            F=eta_all(n,p); absF2=np.abs(F)**2
            beta=np.log2(p/n)
            cross=None
            row=[]
            for k in range(1,9):
                Ak=((absF2**k).sum()-absF2[0]**k)/p
                w=dfact(2*k-1)*n**k
                r=Ak/w
                row.append(f"k{k}:{r:.2f}")
                if r>1 and cross is None: cross=k
            print(f"  n={n:3d} p={p:7d} beta=log2(p/n)={beta:.2f}: crossover k*={cross}  "+" ".join(row))
    print()
    print("="*100)
    print("(B2) k=1 closes by PARSEVAL (=n-n^2/p), NOT by E_2=3n^2-3n. Verify the energy labels.")
    print("="*100)
    for n,plist in [(8,[97,401]),(16,[193,1153])]:
        for p in plist:
            if (p-1)%n: continue
            F=eta_all(n,p); absF2=np.abs(F)**2
            # E_1 energy = (1/p)sum_b |eta_b|^2 (INCLUDING b=0) = n exactly (Parseval). A_1 = n - n^2/p.
            E1=absF2.sum()/p
            A1=(absF2.sum()-absF2[0])/p
            # E_2(mu_n) = additive 2-energy = (1/p)sum_b |eta_b|^4 (INCLUDING b=0); A_2 = that - n^4/p.
            E2=(absF2**2).sum()/p
            A2=((absF2**2).sum()-absF2[0]**2)/p
            print(f"  mu_{n} p={p}: E_1={E1:.3f}(=n={n})  A_1={A1:.3f}(=n-n^2/p)  |  "
                  f"E_2={E2:.2f} (3n^2-3n={3*n*n-3*n})  A_2={A2:.3f}")
            print(f"      => k=1 ratio uses A_1=PARSEVAL(2nd moment, n-n^2/p), 3n^2-3n is the 4th moment(E_2/A_2). MISLABEL CHECK.")
    print()
    print("="*100)
    print("(B3) Does the recursion bound A_k(n) by char-0 WITHOUT assuming A_k(n/2)<=Wick?")
    print("     Telescoping ratio: Young gives <=4^k (trivial n^2k), Wick needs =2^k. Measure actual ratio")
    print("     A_k(2^mu)/A_k(2^{mu-1}) and compare to 2^k (Wick) and 4^k (Young/trivial).")
    print("="*100)
    for n in [16,32,64]:
        p=n*n*n
        while not (isprime(p) and (p-1)%n==0): p+=1
        Fn=eta_all(n,p); Fh=eta_all(n//2,p)
        an=np.abs(Fn)**2; ah=np.abs(Fh)**2
        print(f"  mu_{n}/mu_{n//2} p={p}:")
        for k in [1,2,3,4]:
            Akn=((an**k).sum()-an[0]**k)/p
            Akh=((ah**k).sum()-ah[0]**k)/p
            ratio=Akn/Akh
            print(f"    k={k}: ratio A_k(n)/A_k(n/2)={ratio:7.2f}   Wick-need 2^k={2**k:4d}   Young-allow 4^k={4**k:5d}   "
                  f"{'IN (2^k,4^k]' if 2**k-0.3<=ratio<=4**k+0.3 else 'OUT'}")

if __name__=="__main__":
    main()
