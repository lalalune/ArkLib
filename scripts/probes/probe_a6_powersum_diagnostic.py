#!/usr/bin/env python3
"""
A6 diagnostic-2 — Do the INTEGER power sums P_k = sum_i eta_i^k carry any
information beyond P_1=-1, P_2=p-n that could force max|eta_i| <= C sqrt(n)?

Since n even => -1 in mu_n => periods eta_i are REAL.  So Psi_p(T) is a real
(integer) polynomial with m REAL roots.  This is the Schur-Siegel-Smyth setting:
a degree-m monic integer polynomial with all-real roots, bound the spread.

The trace-problem machinery (Schur 1918) for a degree-m monic integer poly with
all roots in [a,b] gives constraints from P_1, P_2 being integers. The classical
Schur bound: for totally-real algebraic integers, the SMALLEST root and the trace
are linked. But the eta_i are NOT a single algebraic integer's conjugates spanning
a Galois orbit alone -- they ARE a full Galois orbit (Psi_p irreducible over Q
when... actually Psi_p factors per the decomposition group). Let's test.

KEY QUESTIONS:
  Q1. Are the m periods one Galois orbit (Psi_p irreducible / power of irreducible)?
  Q2. P_3, P_4: do they deviate from what max|eta|<=C sqrt(n) + Parseval would force,
      i.e. is there a "fourth-moment" excess that already SEES the tail (like the
      moment ladder), or are P_3,P_4 also rigidly fixed by p,n (=> no new info)?
  Q3. The decisive test: GIVEN P_1=-1, P_2=p-n, and ALL roots real, what is the
      MAXIMUM possible max|root| consistent with these two integer constraints?
      That's an optimization: maximize max|x_i| s.t. sum x_i = -1, sum x_i^2 = p-n,
      m roots.  Answer: one root can be as large as ~ sqrt((m-1)/m * (p-n)) ~ sqrt(p)
      !!  So P_1,P_2 ALONE permit a root of size sqrt(p) >> sqrt(n).  The integer
      constraints do NOT cap the max at sqrt(n).  The cap to sqrt(n)-ish must come
      from HIGHER structure (P_3,P_4,... = all power sums fixed), i.e. from the FULL
      polynomial, which is exactly the domain content again.  Test if P_3,P_4 are
      themselves rigidly p,n-determined (no slack) -- if so, A6 has no lever beyond
      what the explicit period values (=the domain) give.
"""
import math, cmath
from sympy import isprime, Poly, symbols, factor_list, ZZ
import numpy as np

def primitive_root(p):
    phi=p-1; fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def periods(p,n):
    m=(p-1)//n; g=primitive_root(p)
    gm=pow(g,m,p); sub=[]; cur=1
    for _ in range(n): sub.append(cur); cur=cur*gm%p
    tp=2*math.pi/p
    def ps(b):
        return sum(cmath.exp(1j*tp*((b*x)%p)) for x in sub)
    etas=[]; gi=1
    for i in range(m): etas.append(ps(gi)); gi=gi*g%p
    return etas,m,g

def run(p,n):
    etas,m,g=periods(p,n)
    M=max(abs(e) for e in etas)
    # all should be real (n even)
    maxim = max(abs(e.imag) for e in etas)
    re=[e.real for e in etas]
    Pk=[sum(x**k for x in re) for k in range(1,7)]
    # integer-constraint-permitted max root given only P1,P2 and m real roots:
    # maximize x1 s.t. sum=P1, sum sq=P2; others equal => x1 + (m-1)y=P1, x1^2+(m-1)y^2=P2
    # => permitted_max = P1/m + sqrt((m-1)/m)*sqrt(P2 - P1^2/m)
    P1,P2=Pk[0],Pk[1]
    permitted=(P1/m)+math.sqrt((m-1)/m)*math.sqrt(P2-P1*P1/m)
    sqrtn=math.sqrt(n); sqrtp=math.sqrt(p)
    # excess fourth-moment indicator: P4 vs (P2^2/m) [flat] -- kurtosis-like
    flatP4=P2*P2/m
    print(f"p={p} n={n} m={m}: M={M:.3f} M/sqrtn={M/sqrtn:.3f}  maxImag={maxim:.1e}")
    print(f"   P=[{Pk[0]:.1f},{Pk[1]:.1f},{Pk[2]:.1f},{Pk[3]:.3e},{Pk[4]:.3e},{Pk[5]:.3e}]")
    print(f"   permitted max from P1,P2 only = {permitted:.1f} (= ~sqrt(p)={sqrtp:.1f}); ACTUAL M={M:.3f}")
    print(f"   M / permitted = {M/permitted:.4f}   (if ~1, P1,P2 tight; if <<1, higher P_k bind)")
    print(f"   P4 / (P2^2/m) [excess kurtosis ind.] = {Pk[3]/flatP4:.3f}")
    return dict(p=p,n=n,m=m,M=M,permitted=permitted,Pk=Pk)

def find_primes(n,count,pmin):
    out=[]; t=pmin//n+1
    while len(out)<count:
        p=1+n*t
        if isprime(p): out.append(p)
        t+=1
    return out

if __name__=="__main__":
    print("=== A6 power-sum diagnostic ===\n")
    print("Q3: max root permitted by P1,P2 + real + m roots ~ sqrt(p). The ACTUAL")
    print("max is ~sqrt(n log). So the gap is closed by P3,P4,... -- the FULL poly.\n")
    for mu in [3,4,5,6]:
        n=2**mu; pmin=max(50*n**3,1000)
        for p in find_primes(n,2,pmin):
            run(p,n); print()
