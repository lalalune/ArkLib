#!/usr/bin/env python3
"""
#407 C5 — does the moment recursion TELESCOPE? Two obstructions tested:

Recursion (verified exactly in probe_407_conn_c5_recursion_derive.py):
   A_k(n) + A^chi_k(n) = 2 sum_{i=0}^{k} C(2k,2i) M_{i,k-i}(n/2)
where M_{a,b}(n/2) = (1/p) sum_c eta_c(mu_{n/2})^{2a} eta_{c zeta}(mu_{n/2})^{2b}.

For this to give a CLOSED recursion A_k(n) <- {A_*(n/2)}, two things must hold:
 (T1) A^chi_k(n) (the TWIST moment) must reduce to known tower quantities, AND
 (T2) the cross-moments M_{i,k-i} (1<=i<=k-1) must reduce to single-frequency level-(n/2) moments.

We test BOTH.

(T1) A^chi_k(n): the twisted period eta^chi_b(mu_n) = sum_{x in mu_n} chi(x) e_p(bx), chi=quadratic
     char of mu_n. Is A^chi_k(n) = A_k(n) (same value) or another tower object? We compute
     A^chi_k(n) directly and compare to A_k(n), and to char-0 Wick for the twisted sum.

(T2) FACTORIZATION TEST: if eta_c(mu_{n/2}) and eta_{c zeta}(mu_{n/2}) were INDEPENDENT across c,
     then M_{a,b} ~ A_a(n/2)*A_b(n/2)/normalization. Test:
        ratio R_{a,b} := M_{a,b} / ( (something with A_a, A_b) ).
     More precisely test the "independence factorization":
        M_{a,b} =?= (1/p) [sum_c x_c^{2a}] [sum_c y_c^{2b}] / p   -- the product-of-marginals heuristic
     vs the EXACT joint. Report the ratio M_{a,b} / (A_a(n/2)*A_b(n/2)) and whether it -> 1.
"""
import cmath, math
from sympy import primitive_root as pr
from math import comb

def subgroup_step(t, n2, p):
    S=[]; x=1
    for _ in range(n2):
        S.append(x); x=(x*t)%p
    return S

def eta_real(c, S, p):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((c*x)%p)) for x in S).real

def analyze(n, p, kmax=3):
    n2=n//2
    g=int(pr(p)); t=pow(g,(p-1)//n,p)
    Sn = subgroup_step(t, n, p)          # mu_n
    Sn2= subgroup_step((t*t)%p, n2, p)   # mu_{n/2}
    zeta=t
    # quadratic char on mu_n: chi(t^j)=(-1)^j  (so +1 on even powers=mu_{n/2}, -1 on odd)
    # eta^chi_b(mu_n) = A - B  (verified). compute moments + cross-moments + factorization.
    A=[0.0]*p; B=[0.0]*p
    for b in range(1,p):
        A[b]=eta_real(b,Sn2,p); B[b]=eta_real((b*zeta)%p,Sn2,p)
    Ak=[0.0]*(kmax+1); Achi=[0.0]*(kmax+1)
    M={}
    margA=[0.0]*(kmax+1)  # (1/p) sum_c x_c^{2a}  == A_a(n/2)
    for b in range(1,p):
        s=A[b]+B[b]; d=A[b]-B[b]
        for k in range(1,kmax+1):
            Ak[k]+=s**(2*k); Achi[k]+=d**(2*k); margA[k]+=A[b]**(2*k)
        for a in range(0,kmax+1):
            for c in range(0,kmax+1-a):
                M[(a,c)]=M.get((a,c),0.0)+(A[b]**(2*a))*(B[b]**(2*c))
    for k in range(1,kmax+1): Ak[k]/=p; Achi[k]/=p; margA[k]/=p
    for key in M: M[key]/=p
    return Ak, Achi, M, margA, n2

def main():
    cases=[(8,[97,193,401]),(16,[193,353,577,1153]),(32,[353,449,577,1153])]
    kmax=3
    print("="*115)
    print("(T1) TWIST MOMENT  A^chi_k(n)  vs  A_k(n):  is the twist the SAME tower object or different?")
    print("="*115)
    for n,primes in cases:
        print(f"\n--- mu_{n} ---")
        for p in primes:
            Ak,Achi,M,margA,n2=analyze(n,p,kmax)
            row=[]
            for k in range(1,kmax+1):
                r=Achi[k]/Ak[k] if Ak[k] else float('nan')
                row.append(f"k{k}: A={Ak[k]:.2f} Achi={Achi[k]:.2f} (Achi/A={r:.3f})")
            print(f"  p={p:5d}  "+"  ".join(row))
    print()
    print("="*115)
    print("(T2) CROSS-MOMENT FACTORIZATION:  R_{a,b} = M_{a,b} / (A_a(n/2)*A_b(n/2)).")
    print("     If halves were INDEPENDENT, R->1. M_{a,b}=(1/p)sum_c x^{2a}y^{2b}, A_a(n/2)=(1/p)sum_c x^{2a}.")
    print("     [a=k,b=0 endpoints are EXACTLY A_k(n/2); only the (a>=1,b>=1) interior is the new joint object]")
    print("="*115)
    for n,primes in cases:
        print(f"\n--- mu_{n} (level n/2=mu_{n//2}) ---")
        for p in primes:
            Ak,Achi,M,margA,n2=analyze(n,p,kmax)
            # interior cross moments for total degree 2,3
            cells=[]
            for tot in range(2,kmax+1):
                for a in range(1,tot):
                    b=tot-a
                    Mab=M.get((a,b),0.0)
                    fac=margA[a]*margA[b]
                    R=Mab/fac if fac else float('nan')
                    cells.append(f"M_({a},{b})={Mab:.2f}/[{fac:.2f}]=R{R:.3f}")
            print(f"  p={p:5d}  "+"   ".join(cells))

if __name__=="__main__":
    main()
