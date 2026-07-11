#!/usr/bin/env python3
"""
#407 C5 — THE CLOSURE TEST: does the moment recursion give a WORKING descent, or
inherit the SAME alignment obstruction as the L^infty route?

Exact recursion (verified): with M_{a,b}(n/2)=(1/p)sum_c eta_c(mu_{n/2})^{2a} eta_{c zeta}(mu_{n/2})^{2b},
   A_k(n) = -A^chi_k(n) + 2 sum_{i=0}^k C(2k,2i) M_{i,k-i}(n/2).               (*)

To get a CLOSED descent A_k(n) <= F(A_*(n/2)) we must:
   (i) DROP A^chi_k>=0 (it's a sum of even powers >=0), giving the UPPER bound
        A_k(n) <= 2 sum_{i=0}^k C(2k,2i) M_{i,k-i}(n/2).                        (UB)
   (ii) bound the interior cross-moments M_{i,k-i} by single-frequency moments.
The cleanest (ii): Cauchy-Schwarz  M_{i,k-i} = E[x^{2i} y^{2(k-i)}] <= sqrt(E[x^{4i}] E[y^{4(k-i)}])
   = sqrt(A_{2i}(n/2) A_{2(k-i)}(n/2)).   OR the AM-GM / Young:
   x^{2i}y^{2(k-i)} <= (i/k) x^{2k} + ((k-i)/k) y^{2k}  -> M_{i,k-i} <= A_k(n/2).
The Young route gives M_{i,k-i} <= A_k(n/2) for EVERY i, so
   A_k(n) <= 2 A_k(n/2) sum_{i=0}^k C(2k,2i) = 2 A_k(n/2) * 2^{2k-1} = 4^k A_k(n/2).   (Y)
THIS telescopes!  A_k(2^mu) <= 4^{k(mu-1)} A_k(mu_2) = 4^{k(mu-1)} C(2k,k).
But does (Y) give the RIGHT growth? Required (Wick): A_k(n) ~ (2k-1)!! n^k = (2k-1)!! 2^{k mu}.
   (Y) gives 4^{k(mu-1)} C(2k,k) = 2^{2k mu - 2k} C(2k,k) = n^{2k}/4^k * C(2k,k)  -- that's n^{2k} GROWTH
   (quadratic in n, like the TRIVIAL b=0-included bound n^{2k}), NOT n^k.  So (Y) is USELESS
   (it telescopes but to the trivial L^2-trivial bound -> the SAME Johnson wall / no sqrt-cancellation).

TEST PLAN:
 (1) Verify (UB): A_k(n) <= 2 sum_i C(2k,2i) M_{i,k-i}.  (equality holds when A^chi=0; here strict.)
 (2) Compare the THREE closures vs TRUE A_k(n):
       - exact RHS of (*) [needs true A^chi and M],
       - Young telescoped 4^k A_k(n/2) [the only one that closes],
       - the TRUE Wick target (2k-1)!! n^k.
     Show: Young massively OVERSHOOTS (gives ~n^{2k}, trivial), exact needs the un-droppable
     A^chi and the un-factorable M -> the descent does NOT improve on Johnson.
 (3) THE ALIGNMENT DIAGNOSIS: at the worst b (where eta_b max), is A^chi_b large too (twist aligned)?
     The L^infty route died because at b*, A=B (cos=1) so no cancellation. For the MOMENT route,
     the analogue is: the interior cross-moments M_{i,k-i} are dominated by the SAME aligned b's.
     Measure corr between x_c^2 and y_c^2 over c, AND the tail contribution.
"""
import cmath, math
from sympy import primitive_root as pr
from math import comb

def step(t,m,p):
    S=[]; x=1
    for _ in range(m): S.append(x); x=(x*t)%p
    return S
def eta_real(c,S,p):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((c*x)%p)) for x in S).real
def df(m):
    r=1
    for j in range(1,m+1,2): r*=j
    return r

def full(n,p,kmax):
    n2=n//2; g=int(pr(p)); t=pow(g,(p-1)//n,p)
    Sn=step(t,n,p); S2=step((t*t)%p,n2,p); zeta=t
    A=[0.0]*p; B=[0.0]*p; En=[0.0]*p
    for b in range(1,p):
        A[b]=eta_real(b,S2,p); B[b]=eta_real((b*zeta)%p,S2,p); En[b]=eta_real(b,Sn,p)
    # moments of level n
    Ak=[0.0]*(kmax+1)
    # level n/2 single-freq moments up to 2*kmax (for Cauchy-Schwarz)
    An2=[0.0]*(2*kmax+1)
    M={}
    xy_for_corr=[]
    for b in range(1,p):
        e=En[b]; e2=e*e; pw=1.0
        for k in range(1,kmax+1): pw*=e2; Ak[k]+=pw
        ax=A[b]*A[b]
        pw=1.0
        for k in range(1,2*kmax+1): pw*=ax; An2[k]+=pw
        for a in range(0,kmax+1):
            for c in range(0,kmax+1-a):
                M[(a,c)]=M.get((a,c),0.0)+(A[b]**(2*a))*(B[b]**(2*c))
        xy_for_corr.append((A[b]*A[b], B[b]*B[b]))
    for k in range(1,kmax+1): Ak[k]/=p
    for k in range(1,2*kmax+1): An2[k]/=p
    for key in M: M[key]/=p
    # correlation of x^2,y^2 over c
    import statistics as st
    xs=[u for u,_ in xy_for_corr]; ys=[v for _,v in xy_for_corr]
    mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
    cov=sum((u-mx)*(v-my) for u,v in xy_for_corr)/len(xy_for_corr)
    sx=(sum((u-mx)**2 for u in xs)/len(xs))**0.5; sy=(sum((v-my)**2 for v in ys)/len(ys))**0.5
    corr=cov/(sx*sy) if sx*sy else float('nan')
    return Ak, An2, M, corr, n2

def main():
    kmax=3
    print("="*112)
    print("CLOSURE TEST: TRUE A_k(n) vs (a) Young-telescoped 4^k A_k(n/2), (b) Wick (2k-1)!!n^k,")
    print("              (c) Cauchy-Schwarz UB 2 sum_i C(2k,2i) sqrt(A_{2i} A_{2(k-i)})(n/2).")
    print("   corr = Pearson corr of (x_c^2,y_c^2) over c  (=> halves dependent <=> != 0).")
    print("="*112)
    for n,primes in [(8,[193,401]),(16,[577,1153]),(32,[577,1153])]:
        print(f"\n=== mu_{n} (n/2=mu_{n//2}) ===")
        for p in primes:
            Ak,An2,M,corr,n2=full(n,p,kmax)
            print(f"  p={p:5d}  corr(x^2,y^2)={corr:+.3f}")
            for k in range(1,kmax+1):
                wick=df(2*k-1)*n**k
                young=(4**k)*Ak_n2 if False else (4**k)*An2[k]  # A_k(n/2)=An2[k]
                # Cauchy-Schwarz UB
                cs=2*sum(comb(2*k,2*i)*math.sqrt(An2[2*i]*An2[2*(k-i)]) for i in range(0,k+1))
                # exact RHS with the true M (= A_k + A^chi by (*))
                rhs=2*sum(comb(2*k,2*i)*M.get((i,k-i),0.0) for i in range(0,k+1))
                print(f"     k={k}: TRUE A_k(n)={Ak[k]:13.2f}  Wick={wick:13.1f}  "
                      f"Young(4^k A_k(n/2))={young:15.1f}  CS_UB={cs:13.1f}  "
                      f"[Young/Wick={young/wick:6.1f}x]")

if __name__=="__main__":
    main()
