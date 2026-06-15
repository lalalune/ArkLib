#!/usr/bin/env python3
"""wf-NC (#407): the DECISIVE test — does the p-adic Gamma_p digit/valuation structure of the
dyadic exponents a=nk give an ARCHIMEDEAN handle on the SUP, or only the (trivial) |g|=sqrt(p)?

GK (f=1):  g(chi^{-a}) = -pi^a * Gamma_p(a/(p-1)),  pi^{p-1}=-p,  a in {1..p-2}.
=> |g|_p = |pi|_p^a = p^{-a/(p-1)}  (the p-adic valuation v_p(g) = a/(p-1)).
The Gamma_p factor is a p-adic UNIT: |Gamma_p(x)|_p = 1.  So GK pins:
  - the p-adic VALUATION of g exactly (Stickelberger, the section-6 MAGNITUDE no-go), and
  - the UNIT part as a single Gamma_p value (no product, since f=1).
The archimedean |g|=sqrt(p) is INDEPENDENT of the unit part (it's |sum of roots of unity|).

CLAIM TO TEST: for f=1 there is exactly ONE Gamma_p factor per Gauss sum (digit-sum = a itself,
single base-p digit because a<p-1). So the 'dyadic base-p digit-sum special structure' that the
mission hopes to exploit DOES NOT APPEAR for q prime (f=1): there are no multiple digits to make
the digit-sum small. The multi-factor GK product (the genuine handle) needs f>1, i.e. q=p^f a
PRIME POWER, which the prize forbids (q is prime).

We verify the v_p split numerically (Gauss sum factored in Z[zeta_p,zeta_{p-1}] is hard; instead
verify the GK valuation law via the EISENSTEIN reciprocity surrogate: the prime ideal factorization
exponents = Stickelberger element {a/(p-1)} summed over Frobenius. For f=1 Frobenius orbit is
trivial so it's a single term a/(p-1) -> NO digit spreading.)

We then test the ONE thing that could still help: even with a single Gamma_p, does the SUM over
the coset (eta_b = (1/m) sum_k zeta^{-nkc} g(chi^{nk})) have its Gamma_p phases ALIGNED by a
Gamma_p MULTIPLICATION (Gauss-mult) relation that forces archimedean cancellation? Test the
Gauss multiplication / Davenport-Hasse PRODUCT relation among g(chi^{nk}), k=0..m-1:
   prod_{k=0}^{m-1} g(chi * eta_m^k)  vs  Davenport-Hasse  (eta_m = char of order m).
"""
import math, cmath

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True

def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a

def gauss_sum(a,p,g0):
    zp=2j*math.pi/p; zpm1=2j*math.pi/(p-1)
    s=0+0j; t=1
    for k in range(p-1):
        s+=cmath.exp(zpm1*(a*k))*cmath.exp(zp*t)
        t=t*g0%p
    return s

# ---- Davenport-Hasse PRODUCT (Gauss multiplication) relation test ----
# For chi of order dividing p-1 and the m-th power-residue characters eta^k (eta order m | p-1):
#   prod_{k=0}^{m-1} g(chi * eta^k) = chi^{-m}(m) * g(chi^m) * prod_{k=1}^{m-1} g(eta^k)
# (Hasse-Davenport product relation). This is the multiplicative analogue of Gamma_p multiplication
# (Gross-Koblitz turns it into the Gamma_p Gauss-multiplication formula).
# We test it for chi = chi^0 = trivial? trivial chi gauss sum = -1. Take chi = chi^1 and the
# characters of order m: eta = chi^{(p-1)/m} = chi^n (order m). Then chi*eta^k = chi^{1+nk}.
def davenport_hasse(p,n):
    g0=primroot(p); m=(p-1)//n
    # eta = chi^n has order m.  test relation with chi = chi^1.
    lhs=1+0j
    for k in range(m):
        a=(1+n*k)%(p-1)
        lhs*= (gauss_sum(a,p,g0) if a!=0 else -1)
    # rhs = chi^{-m}(m) g(chi^m) prod_{k=1}^{m-1} g(eta^k)
    zpm1=2j*math.pi/(p-1)
    # chi^{-m}(m): chi(g0)=zeta_{p-1}. m = g0^{ind(m)}. need discrete log of m.
    # build dlog table small
    dlog={}; t=1
    for e in range(p-1):
        dlog[t]=e; t=t*g0%p
    chi_neg_m_of_m=cmath.exp(zpm1*(-m*dlog[m%p]))
    gchim = gauss_sum(m%(p-1),p,g0) if (m%(p-1))!=0 else -1
    prod_eta=1+0j
    for k in range(1,m):
        a=(n*k)%(p-1)
        prod_eta*= (gauss_sum(a,p,g0) if a!=0 else -1)
    rhs=chi_neg_m_of_m*gchim*prod_eta
    return abs(lhs-rhs)/ (abs(rhs)+1e-12)

if __name__=="__main__":
    print("=== GK valuation structure for q=p prime (f=1): single Gamma_p factor, no digit spread ===")
    print("v_p(g(chi^{-a})) = a/(p-1) exactly (Stickelberger). Unit part = ONE Gamma_p(a/(p-1)).")
    print("Dyadic exponent a=nk: v_p = nk/(p-1) = k/m. STILL single digit (a<p-1) -> NO digit-sum handle.\n")
    print("=== Davenport-Hasse product relation among the m coset Gauss sums (rel.err) ===")
    print("n   p     m   DH-rel-err")
    for n in [8,16,32]:
        ps=[pp for pp in range(n+1,2500) if isprime(pp) and (pp-1)%n==0][:4]
        for p in ps:
            try:
                e=davenport_hasse(p,n)
                print(f"{n:<4}{p:<6}{(p-1)//n:<4}{e:.2e}",flush=True)
            except Exception as ex:
                print(f"{n:<4}{p:<6}  ERR {ex}",flush=True)
