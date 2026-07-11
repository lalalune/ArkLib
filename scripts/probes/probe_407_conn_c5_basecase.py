#!/usr/bin/env python3
"""
#407 C5 — (b) does the recursion telescope to a mu_2/mu_4 base case, and
            what is the twist moment A^chi_k really?

THE RECURSION (exact):
   A_k(n) + A^chi_k(n) = 2 sum_{i=0}^{k} C(2k,2i) M_{i,k-i}(n/2),        (*)
with endpoints M_{k,0}=M_{0,k}=A_k(n/2) and interior cross-moments M_{i,k-i}.

To close it we'd need (*) to express A_k(n) using only A_*(n/2) (then recurse to mu_2/mu_4).
Two unknowns block this: A^chi_k(n) and the interior M_{i,k-i}. Tests:

(B1) IS THE TWIST A SHIFTED PERIOD?  eta^chi_b(mu_n)=sum_x chi(x) e_p(bx). The quadratic char
     chi on mu_n: chi(x)=x^{n/2}=+-1.  By Gauss-sum/multiplicative-shift,
        sum_{x in mu_n} chi(x) e_p(bx)  is a "twisted" Gauss period.
     Claim to test: eta^chi_b(mu_n) = eta_{b'}(coset) for some coset? Actually
        sum_x chi(x)e_p(bx) over mu_n  = (sum over squares mu_{n/2}) - (sum over non-squares).
     The set of non-squares in mu_n IS zeta*mu_{n/2}. So twist = A - B, already known.
     KEY TEST: is A^chi_k(n) ALSO governed by the SAME char-0 Wick bound (2k-1)!!n^k? If yes,
     the twist is "as good as" the untwisted -> the recursion's two LHS terms are SYMMETRIC and
     one bounds the other. Compute E^chi_k := A^chi_k + (b=0 term) and compare to Wick.
     (b=0: eta^chi_0 = sum_x chi(x) = 0 since equal # of +-1. So A^chi_k = full twisted energy.)

(B2) BASE CASE.  mu_2={1,-1}: eta_b(mu_2)=e_p(b)+e_p(-b)=2cos(2pi b/p) in [-2,2].
     A_k(mu_2)=(1/p)sum_{b!=0}(2cos)^{2k}. EXACT: (1/p)sum_{b=0}^{p-1}(2cos(2pi b/p))^{2k}=C(2k,k)
     (central binomial, the # of closed 2k-walks on Z that return to 0... actually =C(2k,k)).
     minus b=0 term (=4^k/p). So A_k(mu_2)=C(2k,k)-4^k/p -> C(2k,k). Wick: (2k-1)!!*2^k=C(2k,k)*k!...
     check (2k-1)!!*2^k = (2k)!/(k! 2^k) * 2^k = (2k)!/k! ; C(2k,k)=(2k)!/(k!)^2. NOT equal for k>1!
     So mu_2 base ENERGY = C(2k,k), which is SMALLER than Wick (2k-1)!!2^k by a factor k!.
     -> the Wick bound is NOT tight at the base; verify which the tower actually produces.

(B3) THE TELESCOPE TEST.  If we IGNORE the interior cross-moments' correlation and the twist,
     does iterating (*) with the (false) independence M_{i,k-i}~A_i A_{k-i} reproduce Wick or
     diverge? I.e. show concretely that the obstruction (T1/T2) is load-bearing: plug measured
     A_*(n/2) into (*) assuming A^chi=A and M factorizes, predict A_k(n), compare to TRUE A_k(n).
"""
import cmath, math
from sympy import primitive_root as pr
from math import comb, factorial

def step(t,m,p):
    S=[]; x=1
    for _ in range(m): S.append(x); x=(x*t)%p
    return S
def eta_real(c,S,p):
    w=2j*math.pi/p
    return sum(cmath.exp(w*((c*x)%p)) for x in S).real
def df(m):  # double factorial (2k-1)!!
    r=1
    for j in range(1,m+1,2): r*=j
    return r

def energies(n,p,kmax):
    g=int(pr(p)); t=pow(g,(p-1)//n,p)
    S=step(t,n,p)
    Ak=[0.0]*(kmax+1)
    for b in range(1,p):
        e=eta_real(b,S,p); e2=e*e; pw=1.0
        for k in range(1,kmax+1): pw*=e2; Ak[k]+=pw
    return [Ak[k]/p for k in range(kmax+1)]

def twist_energies(n,p,kmax):
    """A^chi_k = (1/p) sum_{b!=0} (eta^chi_b)^{2k}, eta^chi_b = A-B."""
    n2=n//2; g=int(pr(p)); t=pow(g,(p-1)//n,p)
    S2=step((t*t)%p,n2,p); zeta=t
    Ac=[0.0]*(kmax+1)
    for b in range(1,p):
        A=eta_real(b,S2,p); B=eta_real((b*zeta)%p,S2,p); d=A-B; d2=d*d; pw=1.0
        for k in range(1,kmax+1): pw*=d2; Ac[k]+=pw
    return [Ac[k]/p for k in range(kmax+1)]

def main():
    kmax=4
    print("="*100)
    print("(B1) IS THE TWIST AS GOOD AS UNTWISTED? compare twist energy E^chi_k to Wick (2k-1)!!n^k")
    print("     E^chi_k = A^chi_k (b=0 term=0). untwisted A_k for reference.")
    print("="*100)
    for n,primes in [(8,[193,401]),(16,[577,1153]),(32,[577,1153])]:
        wick=[df(2*k-1)*n**k for k in range(0,kmax+1)]
        print(f"\n--- mu_{n}: Wick (2k-1)!!{n}^k = {[wick[k] for k in range(1,kmax+1)]}")
        for p in primes:
            Ak=energies(n,p,kmax); Ac=twist_energies(n,p,kmax)
            print(f"  p={p:5d}:")
            for k in range(1,kmax+1):
                print(f"      k={k}: A_k={Ak[k]:12.2f}  A^chi_k={Ac[k]:12.2f}  Wick={wick[k]:12.1f}   "
                      f"A^chi/Wick={Ac[k]/wick[k]:.3f}  A/Wick={Ak[k]/wick[k]:.3f}")
    print()
    print("="*100)
    print("(B2) BASE CASE mu_2:  A_k(mu_2) should -> C(2k,k) (central binomial), NOT Wick (2k)!/k!")
    print("="*100)
    for p in [101,401,1009,4001]:
        Ak=energies(2,p,kmax)
        cb=[comb(2*k,k) for k in range(0,kmax+1)]
        wick2=[factorial(2*k)//factorial(k) for k in range(0,kmax+1)]  # (2k-1)!!2^k=(2k)!/k!
        print(f"  p={p:5d}: "+"  ".join(
            f"k{k}: A={Ak[k]:.3f}(C={cb[k]}, Wick={wick2[k]})" for k in range(1,kmax+1)))
    print("  mu_4:")
    for p in [101,401,1009]:
        Ak=energies(4,p,kmax)
        wick4=[df(2*k-1)*4**k for k in range(0,kmax+1)]
        print(f"  p={p:5d}: "+"  ".join(f"k{k}: A={Ak[k]:.2f}(Wick={wick4[k]})" for k in range(1,kmax+1)))

if __name__=="__main__":
    main()
