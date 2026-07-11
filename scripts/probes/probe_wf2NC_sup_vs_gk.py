#!/usr/bin/env python3
"""wf-NC (#407) DECISIVE: does the GK unit-phase info CONSTRAIN the SUP below the
phase-free ceiling, or does the worst case already saturate everything GK fixes?

eta_b = (1/m)( -1 + sum_{k=1}^{m-1} zeta_{p-1}^{-nkc} U(nk) sqrt(p) ),  b=g0^c.
The ONLY archimedean constraints GK/DH impose on {U(nk)} are:
  (A) |U(nk)|=1                                    (the trivial |g|=sqrt(p)),
  (B) U(-nk)=conj(U(nk)) with U(nk)U(-nk)=+1       (reflection, = char-0 antipodal, ALREADY refuted),
  (C) prod_k U(nk) fixed by Davenport-Hasse        (a PRODUCT constraint; does it bound the SUP?).
Everything else about U(nk) is a p-adic UNIT congruence with NO archimedean content.

TEST: build the SUP over c with the TRUE phases, vs the SUP achievable by ADVERSARIAL phases that
satisfy ONLY (A)+(B) [reflection] — and ONLY (A)+(B)+(C) [+ DH product]. If true-SUP ~ adversarial-SUP
under (A)+(B), then GK's reflection is the entire archimedean handle (and it's the refuted antipodal one).
If (C) further drops the adversarial-SUP toward the true value, DH would be a genuine new handle.
"""
import math, cmath, random

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
        s+=cmath.exp(zpm1*(a*k))*cmath.exp(zp*t); t=t*g0%p
    return s

def sup_of(U,m,p,sp):
    # U: dict k->unit phase (complex, |.|=1) for k=1..m-1
    zpm1=2j*math.pi/(p-1); n=(p-1)//m
    B=0.0
    for c in range(m):
        s=-1.0+0j
        for k in range(1,m):
            s+=cmath.exp(-zpm1*(n*k*c))*U[k]*sp
        B=max(B,abs(s)/m)
    return B

def analyze(n,p,trials=4000):
    g0=primroot(p); m=(p-1)//n; sp=math.sqrt(p)
    Utrue={}
    for k in range(1,m):
        a=(n*k)%(p-1)
        Utrue[k]=gauss_sum(a,p,g0)/sp
    Btrue=sup_of(Utrue,m,p,sp)
    # adversarial under (A) only: random phases
    bestA=0.0
    for _ in range(trials):
        U={k:cmath.exp(2j*math.pi*random.random()) for k in range(1,m)}
        bestA=max(bestA,sup_of(U,m,p,sp))
    # adversarial under (A)+(B) reflection: U[m-k]=conj(U[k]), pick free k<=m/2
    bestB=0.0
    half=[k for k in range(1,m) if k<=m-k]
    for _ in range(trials):
        U={}
        for k in half:
            ph=cmath.exp(2j*math.pi*random.random())
            U[k]=ph
            if (m-k)!=k and (m-k) in range(1,m): U[m-k]=ph.conjugate()
        # k==m-k self-paired: U[k]^2=+1 => U[k]=+-1
        for k in half:
            if (m-k)==k: U[k]=random.choice([1.0,-1.0])
        bestB=max(bestB,sup_of(U,m,p,sp))
    return Btrue,bestA,bestB,m,sp

if __name__=="__main__":
    random.seed(1)
    print("n   p     m   B_true/sqrt(p-n)  advSUP(A)/sqrt  advSUP(A+B refl)/sqrt   true/advA  true/advB")
    for n,plist in [(8,[41,73,89,97]),(16,[97,113,193]),(32,[97,193,257])]:
        for p in plist:
            if not(isprime(p) and (p-1)%n==0): continue
            Bt,bA,bB,m,sp=analyze(n,p)
            s=math.sqrt(p-n)
            print(f"{n:<4}{p:<6}{m:<4}{Bt/s:<18.4f}{bA/s:<16.4f}{bB/s:<24.4f}{Bt/bA:<11.3f}{Bt/bB:.3f}",flush=True)
