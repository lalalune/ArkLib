#!/usr/bin/env python3
"""
#407 C5 — pin the MECHANISM: why k=1 telescopes exactly (ratio=2) but k>=2 does not.

From (*):  A_k(n) + A^chi_k(n) = 2 sum_{i=0}^k C(2k,2i) M_{i,k-i}(n/2).
Endpoints i=0,k give 2*[M_{0,k}+M_{k,0}] = 2*2*A_k(n/2) = 4 A_k(n/2) (since M_{k,0}=M_{0,k}=A_k(n/2)).
Interior i=1..k-1 give the cross-moment inflation 2 sum_{i=1}^{k-1} C(2k,2i) M_{i,k-i}.

k=1: NO interior term. A_1(n)+A^chi_1(n) = 4 A_1(n/2).  And A^chi_1(n)=A_1(n/2)*? -- measure.
     Actually for k=1, A^chi_1(n) = (1/p)sum (A-B)^2 = A_1(n/2)+A_1(n/2)-2cross = 2A_1(n/2)-2E[AB].
     And A_1(n)=2A_1(n/2)+2E[AB]. So A_1(n)/A_1(n/2) = 2 + 2E[AB]/A_1(n/2). Measure E[AB]:
     it is the cross-correlation of the two halves at order 1 -- which is ~0 (Weil/Parseval),
     giving ratio EXACTLY 2. THIS is the proven part.

k>=2: the interior cross-moments M_{i,k-i} (i,k-i>=1) are NONZERO and NOT equal to a clean
      multiple of A_k(n/2). Their sum is the 'binomial inflation' that pushes the ratio above 2^k.
      Measure, per (n,p,k): the endpoint contribution 4 A_k(n/2), the interior contribution,
      and A^chi_k. Show interior+(-A^chi) is the UNCONTROLLED residual.

This isolates EXACTLY where the descent breaks: the order->1 cross-correlation E[AB]~0 is provable
(=> k=1 clean), but the order->k joint cross-moments are the open higher-order decorrelation.
"""
import numpy as np
from sympy import primitive_root as pr
from math import comb

def periods_halves(n,p):
    """return A[b]=eta_b(mu_{n/2}), B[b]=eta_{b zeta}(mu_{n/2}) for all b (real for 4|n)."""
    n2=n//2; g=int(pr(p)); t=pow(g,(p-1)//n,p)
    # mu_{n/2} indicator
    ind=np.zeros(p); x=1; t2=(t*t)%p
    for _ in range(n2): ind[x]+=1.0; x=(x*t2)%p
    F=np.conjugate(np.fft.fft(ind))   # F[b]=eta_b(mu_{n/2})
    A=F.real.copy()
    zeta=t
    # B[b]=eta_{b zeta}(mu_{n/2}) = A[(b*zeta)%p]
    idx=(np.arange(p)*zeta)%p
    B=A[idx]
    return A,B

def df(m):
    r=1
    for j in range(1,m+1,2): r*=j
    return r

def main():
    kmax=4
    print("="*108)
    print("MECHANISM: A_k(n) = 4 A_k(n/2)  [endpoints]  +  INTERIOR  -  A^chi_k(n).")
    print("  endpoint ratio contribution = 4 (fixed). interior = 2 sum_{i=1}^{k-1} C(2k,2i) M_{i,k-i}.")
    print("  For Wick (ratio=2^k) we need: 4 + interior/A_k(n/2) - A^chi/A_k(n/2) = 2^k.")
    print("="*108)
    for n,primes in [(8,[193,401]),(16,[577,1153]),(32,[1153,2113]),(64,[2113,8129])]:
        for p in primes:
            if (p-1)%n: continue
            A,B=periods_halves(n,p)
            # per-b: s=A+B (level n period), d=A-B (twist)
            s=A+B; d=A-B
            s[0]=A[0]+B[0]  # b=0; will drop below
            # build moments dropping b=0
            mask=np.ones(p); mask[0]=0.0
            def mom(arr,k): return ((arr**(2*k))*mask).sum()/p
            print(f"\n  mu_{n} p={p}:")
            for k in range(1,kmax+1):
                Ak=mom(s,k)            # A_k(n)
                Achi=mom(d,k)          # A^chi_k(n)
                Akn2=mom(A,k)          # A_k(n/2) (single freq, = M_{k,0})
                # interior cross-moment sum
                interior=0.0
                for i in range(1,k):
                    Mi=(((A**(2*i))*(B**(2*(k-i))))*mask).sum()/p
                    interior+=2*comb(2*k,2*i)*Mi
                # check identity Ak+Achi == 4 Akn2 + interior
                ident=4*Akn2+interior-(Ak+Achi)
                ratio=Ak/Akn2
                wickr=2**k
                print(f"    k={k}: A_k(n)/A_k(n/2)={ratio:6.2f} (Wick-need 2^k={wickr})  "
                      f"endpt=4.00 interior/Akn2={interior/Akn2:6.2f} A^chi/Akn2={Achi/Akn2:6.2f}  "
                      f"[id err={ident:.2e}]")

if __name__=="__main__":
    main()
