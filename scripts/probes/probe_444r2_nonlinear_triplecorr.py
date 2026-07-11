#!/usr/bin/env python3
"""
probe_444r2_nonlinear_triplecorr.py (#444) -- LEVER (4): phase-aware 3rd-order objects on the
Gauss periods {eta_b}, eta_b = sum_{x in mu_n} e_p(b x).  GOAL: find a 3rd-order aggregate that
does NOT telescope to q*E_r (= the dead moment wall) and is sub-maximal in a way E_2 is not.

We compute EXACTLY (integer FFT-free where feasible; here exact complex via mpmath-free numpy at
moderate p, all integers mod p for the index arithmetic) several candidate aggregates and classify
each: (T) telescopes to a closed form independent of subgroup structure -> DEAD;
        (S) structural (depends on subgroup) and possibly sub-maximal -> candidate.

Candidates:
  A0  T_unsigned = sum_{a,b} eta_a eta_b eta_{-a-b}        [predicted = p^2 * n exactly -> DEAD]
  A1  S3 = sum_{b!=0} eta_b^3   (eta real since 4|n)        [= p * Z3, Z3=#zero-sum ordered triples in mu_n]
  A2  S3abs = sum_{b!=0} |eta_b|^3                          [the 3rd ABSOLUTE moment -- NOT a poly in eta]
  A3  M = max_b |eta_b|         [the target]
  A4  the "phase-aware ratio"  S3 / S3abs  (cancellation index in the cube)
  A5  signed mixed  sum_{a,b!=0, a+b!=0} eta_a eta_b eta_{-a-b}  (= T_unsigned minus boundary)

The decisive question (rule-5e): is A2 (|eta|^3) controlled by something STRICTLY below the
moment-implied M from E_2?  i.e. does S3abs / (something) give a better M certificate than
M <= (q E_2)^{1/2} ?   We compare M against:
   moment_2  : sqrt(E_2)            (the L2 / dead wall, = sqrt(2 n - ...) per period scale)
   moment_3  : (S3abs)^{1/3} bound? no -- |eta|^3 <= M * |eta|^2, so S3abs <= M * (p E_2-ish).
   Holder    : M = lim (sum|eta|^{2r})^{1/2r}; 3rd gives M >= (S3abs / (#nonzero))^{1/3}.
"""
import numpy as np
from math import sqrt

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_factors(n):
    s=set(); d=2
    while d*d<=n:
        while n%d==0: s.add(d); n//=d
        d+=1
    if n>1: s.add(n)
    return s

def subgroup(p,n):
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=[]; x=1
        for _ in range(n): x=x*h%p; S.append(x)
        if len(set(S))==n: return sorted(S)
    raise RuntimeError(f"no mu_{n} in F_{p}")

def find_prime(n, beta):
    t=int(round(n**beta)); p=t-(t%n)+1
    while p<=t or not isprime(p): p+=n
    return p

def eta_array(p, S):
    # eta_b = sum_{x in S} e_p(b x), exact via numpy complex (double; p moderate)
    b=np.arange(p)
    eta=np.zeros(p, dtype=np.complex128)
    ang=2j*np.pi/p
    for x in S:
        eta+=np.exp(ang*((b*x)%p))
    return eta

def zero_sum_ordered_triples(p,n,S):
    # Z3 = #{(x,y,z) in S^3 : x+y+z = 0 mod p}, EXACT integer
    Sset=set(S); Z=0
    for x in S:
        for y in S:
            if (-(x+y))%p in Sset: Z+=1
    return Z

def report(n, beta):
    p=find_prime(n,beta)
    S=subgroup(p,n)
    # rule-3 / correlation gate: exclude correlated dirs (mu_n has -1 iff 4|n).
    eta=eta_array(p,S)
    eta0=eta.copy(); eta0[0]=0  # b != 0
    mag2=np.abs(eta0)**2
    M=sqrt(mag2.max())
    E2=float((mag2**2).sum())/p          # A_2 raw-ish per-period (sum |eta|^4 / p)
    E1=float(mag2.sum())/p               # = n - n^2/p
    # A0 telescoping check via direct double sum over a (use convolution): T_unsigned
    # T = sum_{a} eta_a * (conv eta*eta at -a). Use that eta_{-a-b}=conj? no, e_p so eta_{-c}=conj(eta_c).
    # sum_{a,b} eta_a eta_b eta_{-a-b}: let C[k] = sum_{a+b=k} eta_a eta_b = (eta conv eta)[k] (cyclic).
    conv = np.fft.ifft(np.fft.fft(eta)**2)*p   # cyclic conv with our normalization: (e*e)[k]=sum_{a} eta_a eta_{k-a}
    # careful: np ifft(fft(x)*fft(x)) = cyclic conv / len? We want sum_{a} eta_a eta_{k-a}.
    conv = np.fft.ifft(np.fft.fft(eta)*np.fft.fft(eta))*p / p  # = cyclic conv exactly
    # T_unsigned = sum_k C[k]*eta_{-k} = sum_k conv[k]*eta[(-k)%p]
    Tuns = np.real(np.sum(conv*eta[(-np.arange(p))%p]))
    # A1 S3 (eta real if 4|n): sum_{b!=0} eta_b^3
    S3 = float(np.real((eta0**3).sum()))
    Z3 = zero_sum_ordered_triples(p,n,S)
    # identity check: sum_{all b} eta_b^3 = p * Z3  (eta_b^3 = sum_{x,y,z} e_p(b(x+y+z)); sum_b -> p*[x+y+z=0])
    S3all = float(np.real((eta**3).sum()))
    # A2 S3abs
    S3abs = float((np.abs(eta0)**3).sum())
    # certificates for M
    Lhol3 = (S3abs/ (p-1))**(1/3)         # weak Holder lower bound on M (mean of |eta|^3)
    L2cert = sqrt(E1)                       # rms scale
    print(f"n={n:>4} p={p} (beta={beta}) idx_m=(p-1)/n={(p-1)//n}")
    print(f"   M={M:.4f}  M/sqrt(n)={M/sqrt(n):.4f}   sqrt(2n)={sqrt(2*n):.4f}")
    print(f"   A0 T_unsigned={Tuns:.3e}   p^2*n={p*p*n:.3e}   ratio={Tuns/(p*p*n):.6f}  [DEAD if ~1]")
    print(f"   A1 S3all={S3all:.3e}  p*Z3={p*Z3:.3e}  Z3={Z3}  ratio={S3all/(p*Z3) if Z3 else float('nan'):.4f}")
    print(f"   A1 S3(b!=0)={S3:.4e}    A2 S3abs={S3abs:.4e}   |S3|/S3abs (cancel idx)={abs(S3)/S3abs:.4f}")
    print(f"   3rd-moment cert (S3abs/(p-1))^1/3 = {Lhol3:.4f}  (vs M={M:.4f}, ratio {Lhol3/M:.4f})")
    print()
    return dict(n=n,p=p,M=M,Msn=M/sqrt(n),Tuns=Tuns,p2n=p*p*n,S3=S3,S3abs=S3abs,Z3=Z3,cancel=abs(S3)/S3abs)

if __name__=="__main__":
    print("="*100)
    print("LEVER 4: phase-aware 3rd-order aggregates of Gauss periods. Telescope-test + cancellation idx.")
    print("="*100)
    rows=[]
    for n in [8,16,32,64,128]:
        rows.append(report(n,4.0))
    print("="*100)
    print("SUMMARY: cancellation index |S3|/S3abs (how much the SIGNED cube cancels vs absolute);")
    print("  Z3/n (zero-sum ordered triple density), and whether A0 telescopes (ratio->1 = DEAD).")
    print(f"{'n':>5}{'M/sqrtn':>10}{'A0ratio':>10}{'Z3':>8}{'Z3/n':>8}{'cancel|S3|/S3abs':>18}")
    for r in rows:
        print(f"{r['n']:>5}{r['Msn']:>10.4f}{r['Tuns']/r['p2n']:>10.5f}{r['Z3']:>8}{r['Z3']/r['n']:>8.3f}{r['cancel']:>18.4f}")
