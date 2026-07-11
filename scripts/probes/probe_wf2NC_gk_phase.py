#!/usr/bin/env python3
"""wf-NC (#407): the GK PHASE handle on max_b |eta_b|.

eta_b = (1/m) sum_{k=0}^{m-1} zeta_{p-1}^{-nkc} g(chi^{nk}),  b=g0^c, |g(chi^{nk})|=sqrt(p) (k!=0).
Write g(chi^a) = sqrt(p) * U(a), |U(a)|=1 the UNIT PHASE.  Gross-Koblitz pins U(a) via Gamma_p.
The SUP question: does the family {U(nk)}_k have phase structure (forced by the p-adic Gamma_p
digit relations: reflection U(a)U(-a)=chi^a(-1), Hasse-Davenport multiplication) that constrains
the worst-case coherent sum sum_k zeta^{-nkc} U(nk) below the trivial m*sqrt(p)?

We DON'T need Gamma_p numerically to read the phases (the complex Gauss sum gives them); we use
GK's KNOWN relations as the structural constraints and test which ones bite the SUP:
 (R1) reflection g(chi^a)g(chi^{-a}) = chi^a(-1) p   => U(a)U(-a) = chi^a(-1) in {+-1}.
 (R2) Hasse-Davenport (lifting): not available for f=1 single field; skip.
 (R3) the dyadic indices a=nk: chi^a(-1)=(-1)^{ (p-1)/2 * nk / ... }; since n even and (p-1)=nm,
      chi^{nk}(-1) = (-1)^{ nk * (p-1)/2 / (p-1) }... compute directly = (g0^{(p-1)/2})^{... }.

Decision: is there a phase-coherence ceiling from R1 (antipodal pairing) that beats trivial?
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

def analyze(n,p):
    g0=primroot(p); m=(p-1)//n
    zpm1=2j*math.pi/(p-1)
    # unit phases U(nk) = g(chi^{nk})/sqrt(p) for k=1..m-1; U for k=0: g(chi^0)=-1 (the +1 in 1_set? )
    sp=math.sqrt(p)
    U={}
    for k in range(1,m):
        a=(n*k)%(p-1)
        U[k]=gauss_sum(a,p,g0)/sp
    # R1 reflection check: pairs k and m-k give a=nk and n(m-k)=(p-1)-nk = -nk.
    # U(nk)U(-nk)=chi^{nk}(-1). chi(g0)=zeta_{p-1}, chi^{nk}(-1): -1=g0^{(p-1)/2}, so =zeta^{nk(p-1)/2}=(-1)^{nk}=+1 (n even).
    r1err=0.0
    for k in range(1,m):
        km=(m-k)%m
        if km==0:  # a=0 partner -> skip (self/identity char)
            continue
        prod=U[k]*U[km]
        chi_at_m1=cmath.exp(zpm1*(n*k*((p-1)//2)))  # zeta_{p-1}^{nk(p-1)/2}
        r1err=max(r1err,abs(prod-chi_at_m1))
    # Build eta_b via phases, find max over c, and ALSO compute the trivial ceiling & the
    # "antipodal-paired" ceiling (pair k with m-k: their contributions are zeta^{-nkc}U(nk)+zeta^{nkc}U(-nk)
    # = 2 Re( zeta^{-nkc} U(nk) ) when U(-nk)=conj(U(nk)) which holds since gauss sum of conj char = conj).
    Bs=[]
    for c in range(m):
        s=-1.0+0j  # k=0 term: g(chi^0)=sum_{t!=0} e_p(t)*1 = -1
        for k in range(1,m):
            s+=cmath.exp(-zpm1*(n*k*c))*U[k]*sp
        Bs.append(abs(s)/m)
    B=max(Bs)
    triv=( -1 + (m-1)*sp )/m  # all phases coherent
    return B,triv,r1err,m,sp

if __name__=="__main__":
    print("n   p     m   B/sqrt(p-n)  trivCeil/sqrt(p-n)  B/trivCeil  R1reflErr",flush=True)
    for n in [8,16,32]:
        ps=[pp for pp in range(n+1,4000) if isprime(pp) and (pp-1)%n==0][:5]
        for p in ps:
            B,triv,r1,m,sp=analyze(n,p)
            snn=math.sqrt(p-n)
            print(f"{n:<4}{p:<6}{m:<4}{B/snn:<13.4f}{triv/snn:<20.4f}{B/triv:<12.4f}{r1:.2e}",flush=True)
