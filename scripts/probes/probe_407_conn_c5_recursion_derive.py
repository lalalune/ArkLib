#!/usr/bin/env python3
"""
#407 CONNECTION C5 — DERIVE the exact moment recursion from the parallelogram tower.

Setup. mu_n = mu_{n/2} ⊔ zeta*mu_{n/2}, zeta a fixed n-th root not in mu_{n/2}.
For frequency b: A(b) = eta_b(mu_{n/2}),  B(b) = eta_{b*zeta}(mu_{n/2}).
  eta_b(mu_n)     = A(b) + B(b)
  eta^chi_b(mu_n) = A(b) - B(b)
For 4|n, A,B are REAL (each coset is negation-closed). So all periods are real.

Now: as b ranges over F_p^*, the pair (A(b), B(b)) = (eta_b(mu_{n/2}), eta_{b zeta}(mu_{n/2})).
Both coordinates are LEVEL-(n/2) periods but at frequencies b and b*zeta.

KEY observation for the moment sum.
   A_k(n) := (1/p) sum_{b!=0} |eta_b(mu_n)|^{2k} = (1/p) sum_{b!=0} (A(b)+B(b))^{2k}   [real]
Define the JOINT level-(n/2) "cross-moments" indexed by the b-orbit:
   C_{a,b}(n/2; zeta) := (1/p) sum_{c!=0} eta_c(mu_{n/2})^{2a} eta_{c zeta}(mu_{n/2})^{2b}  (real, 4|n)
Expanding (A+B)^{2k} = sum_{j=0}^{2k} C(2k,j) A^j B^{2k-j}:
   A_k(n) = (1/p) sum_b sum_j C(2k,j) A(b)^j B(b)^{2k-j}.
Likewise the TWIST moment A^chi_k(n) := (1/p) sum_b (A-B)^{2k} = sum_j C(2k,j) (-1)^{2k-j} A^j B^{2k-j}.

ADDING the untwisted + twisted moments kills ODD j (the (-1)^{2k-j} = (-1)^j flips sign on odd j):
   A_k(n) + A^chi_k(n) = (2/p) sum_b sum_{j even} C(2k,j) A(b)^j B(b)^{2k-j}
                       = 2 sum_{i=0}^{k} C(2k,2i) * M_{i,k-i}
   where M_{a,b} := (1/p) sum_c eta_c(mu_{n/2})^{2a} * eta_{c zeta}(mu_{n/2})^{2b}.
This is the k=1 parallelogram law's GENERALIZATION:
   k=1: A_1(n)+A^chi_1(n) = 2[ C(2,0) M_{0,1} + C(2,2) M_{1,0} ] = 2[ M_{0,1}+M_{1,0} ] = 2[A_1(n/2)+A_1(n/2)]
        (since M_{1,0}=M_{0,1}=A_1(n/2) by the zeta-shift being a bijection on b!=0). ✓ matches parallelogram.

So the OPEN question: is A^chi_k(n) controllable? And are the cross-moments M_{a,b} (a,b>=1)
reducible to single-frequency level-(n/2) moments, or are they a genuinely NEW joint object?

This probe COMPUTES all of: A_k(n), A^chi_k(n), the M_{a,b}, and checks the identity
   A_k(n) + A^chi_k(n) = 2 sum_i C(2k,2i) M_{i,k-i}
exactly, then asks whether M_{a,b} factorizes / telescopes.
"""
import cmath, math
from sympy import primitive_root as pr
from math import comb

def subgroup_mu(n, p):
    g = int(pr(p))
    t = pow(g, (p-1)//n, p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*t)%p
    return S, g, t

def eta_real(c, S, p):
    """real Gauss period (4|n => real); return real part (im ~ 0)."""
    w=2j*math.pi/p
    v=sum(cmath.exp(w*((c*x)%p)) for x in S)
    return v.real

def analyze(n, p, kmax=3):
    assert (p-1)%n==0
    n2=n//2
    Sn, g, t = subgroup_mu(n, p)         # mu_n
    Sn2 = [pow(x,1,p) for x in Sn if True]  # placeholder
    # mu_{n/2}: the squares-coset = first n2 elements stepping by t^2
    t2=(t*t)%p
    Sn2=[]; x=1
    for _ in range(n2):
        Sn2.append(x); x=(x*t2)%p
    zeta=t  # generator of mu_n, zeta not in mu_{n/2} (odd power)
    # For each b, A(b)=eta_b(mu_{n/2}), B(b)=eta_{b zeta}(mu_{n/2})
    A=[0.0]*p; B=[0.0]*p
    EtaN=[0.0]*p   # eta_b(mu_n) directly (cross-check)
    for b in range(1,p):
        A[b]=eta_real(b, Sn2, p)
        B[b]=eta_real((b*zeta)%p, Sn2, p)
        EtaN[b]=eta_real(b, Sn, p)
    # cross-check A+B == eta_b(mu_n)
    maxerr=max(abs(A[b]+B[b]-EtaN[b]) for b in range(1,p))
    # moments
    Ak=[0.0]*(kmax+1); Achi=[0.0]*(kmax+1)
    # M_{a,b} for a+b<=kmax
    M={}
    for b in range(1,p):
        ab=A[b]+B[b]; sub=A[b]-B[b]
        for k in range(1,kmax+1):
            Ak[k]+=ab**(2*k); Achi[k]+=sub**(2*k)
        for a in range(0,kmax+1):
            for c in range(0,kmax+1-a):
                M[(a,c)]=M.get((a,c),0.0)+ (A[b]**(2*a))*(B[b]**(2*c))
    for k in range(1,kmax+1): Ak[k]/=p; Achi[k]/=p
    for key in M: M[key]/=p
    return Ak, Achi, M, maxerr, n2

def main():
    cases=[(8,[41,73,97,193,401]),
           (16,[97,113,193,353,577,1153]),
           (32,[193,257,353,449,577,1153])]
    kmax=3
    print("="*110)
    print("DERIVED IDENTITY CHECK:  A_k(n) + A^chi_k(n) == 2 * sum_{i=0}^{k} C(2k,2i) * M_{i,k-i}")
    print("  (M_{a,b} = (1/p) sum_c eta_c(mu_{n/2})^{2a} eta_{c zeta}(mu_{n/2})^{2b})")
    print("="*110)
    for n, primes in cases:
        print(f"\n=== mu_{n}  (level n/2 = mu_{n//2}) ===")
        for p in primes:
            Ak, Achi, M, maxerr, n2 = analyze(n, p, kmax)
            print(f"  p={p:5d}  (A+B==eta_n maxerr={maxerr:.1e})")
            for k in range(1,kmax+1):
                lhs = Ak[k]+Achi[k]
                rhs = 2*sum(comb(2*k,2*i)*M.get((i,k-i),0.0) for i in range(0,k+1))
                # also: single-freq level n/2 moment A_k(n/2) = M_{k,0} = M_{0,k}
                Ak_n2 = M.get((k,0),0.0)
                Ak_n2_b = M.get((0,k),0.0)
                ok = "OK" if abs(lhs-rhs)<1e-5*max(1,abs(lhs)) else "MISMATCH"
                print(f"    k={k}: A_k(n)={Ak[k]:12.3f}  A^chi_k={Achi[k]:12.3f}  "
                      f"LHS={lhs:12.3f}  RHS={rhs:12.3f}  {ok}   "
                      f"[A_k(n/2)=M_(k,0)={Ak_n2:.3f}, M_(0,k)={Ak_n2_b:.3f}]")

if __name__=="__main__":
    main()
