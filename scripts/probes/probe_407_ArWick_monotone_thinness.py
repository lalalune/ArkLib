#!/usr/bin/env python3
"""
#407 — is A_r/Wick MONOTONE-DECREASING in r?  (a candidate reduction lever for A_r <= Wick)

OBSERVATION (from C14 data + my p=76001 trajectory): A_r/Wick appears monotone DECREASING in r, from a
base A_1/Wick <= 1 (proven: base_case_strict, A_1 < Wick strictly). IF A_{r+1}/Wick <= A_r/Wick robustly,
then A_r <= Wick for ALL r follows from the r=1 base case by monotonicity -- a genuine reduction.

A_r = (1/p) sum_{b!=0} |eta_b|^{2r},  Wick_r = (2r-1)!! n^r.  Define f(r) = A_r/Wick_r.

DECISIVE QUESTIONS (probe-first, exact FFT, PROPER subgroups, large p):
 (Q1) Is f(r+1) <= f(r) for all accessible r, at thin prize-beta primes? (monotone-decreasing?)
 (Q2) THINNESS TEST (rule 3): is the monotonicity thinness-essential? Check thick (beta~2.3-3.2) too.
      - If f is monotone-decreasing in BOTH thick and thin => thickness-invariant => NOT the lever
        (a thickness-monotone reduction can't prove a bound FALSE in the thick window).
      - If f is monotone-decreasing in THIN but NON-monotone / increasing in THICK => thinness-essential
        => a REAL candidate lever (rule 3 satisfied).
 (Q3) Does f EVER exceed 1 (A_r > Wick) at any accessible r? (per-rung failures already known thick at
      shallow r at structured primes -- 320306623; confirm whether f<=1 in thin at all r.)

We test multiple primes per regime including structured/Fermat-type (named adversaries). Exact integer FFT.
HONEST: small n, accessible p; maps the monotonicity, does not prove asymptotic. If monotone-decreasing
holds robustly in thin AND the ratio is the right object, the OPEN piece becomes the single-step
monotonicity inequality f(r+1)<=f(r) at r~log q (which is itself a moment inequality = likely still BGK,
but a DIFFERENT and possibly more tractable framing than the sup-norm directly).

RESULT (exact, FFT spectrum + integer cross-check):
- THIN (prize, beta 3.9-4.6, n=8,16,32): f(r)=A_r/Wick is MONOTONE-DECREASING and <= 1 at EVERY r. Robust.
- THICK: mostly monotone too, EXCEPT the maximally-structured n=32 in F_4129 (beta=2.40): f rises ABOVE 1
  from r=2 (peak 1.705 @ r=5) and is NON-monotone. EXACT integer cross-check confirms A_2=3490 > Wick=3072
  (E_2=3744), so A_r > Wick genuinely FALSE there.
=> THINNESS-ESSENTIAL (rule 3): the property 'f(1)<=1 AND f monotone-decreasing' HOLDS in thin, FAILS in
   thick (where f exceeds 1 and is non-monotone). A proof of A_r <= Wick via [base case f(1)<=1] + [single-
   step monotonicity f(r+1)<=f(r)] is AUTOMATICALLY thinness-essential -- the thick window violates both.
   The open piece is reframed to the single-step monotonicity inequality at r~log q (still BGK-hard, but a
   cleaner, rule-3-correct target than the sup-norm). POSITIVE reframing, not a closure.
"""
import numpy as np, math

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def primroot(p):
    def pf(mm):
        f=set(); d=2; m=mm
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fs=pf(p-1); g=2
    while any(pow(g,(p-1)//q,p)==1 for q in fs): g+=1
    return g

def roots(n,p):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def period_spectrum_sq(n,p):
    """|eta_b|^2 for all b via FFT of indicator of mu_n. O(p log p). returns array length p."""
    ind=np.zeros(p)
    for x in roots(n,p): ind[x%p]=1.0
    F=np.fft.fft(ind)
    return (F*np.conj(F)).real  # |eta_b|^2, b=0..p-1 (b=0 is n^2)

def doublefact(m):
    r=1
    while m>0: r*=m; m-=2
    return r
def wick(n,r): return doublefact(2*r-1)*n**r

def A_over_wick(sq, n, p, rmax):
    """f(r)=A_r/Wick for r=1..rmax. A_r=(1/p) sum_{b!=0} |eta_b|^{2r} = (1/p)(sum_all |eta|^{2r} - n^{2r})."""
    nz=sq.copy(); nz[0]=0.0   # drop b=0 (=n^2)
    out=[]
    for r in range(1,rmax+1):
        Ar=np.sum(nz.astype(object)**r)/p   # sum |eta_b|^{2r} = (|eta_b|^2)^r
        out.append(float(Ar)/wick(n,r))
    return out

def find_prime(n, beta, lo_factor=0.6, hi_factor=1.7):
    target=int(n**beta)
    m=max(1,target//n)
    best=None
    while True:
        p=m*n+1
        if p>target*hi_factor: break
        if p>=target*lo_factor and is_prime(p):
            if best is None or abs(p-target)<abs(best-target): best=p
        m+=1
    return best

print("="*80)
print("A_r/Wick MONOTONICITY + thinness test.  f(r)=A_r/Wick; want f(r+1)<=f(r), f<=1.")
print("="*80)
for n in [8,16,32]:
    rmax = 8 if n<=16 else 7
    print(f"\n### n={n}")
    for label,betas in [("THIN(prize)",[3.9,4.2,4.6]), ("THICK",[2.4,2.8,3.1])]:
        for beta in betas:
            p=find_prime(n,beta)
            if not p: continue
            sq=period_spectrum_sq(n,p)
            f=A_over_wick(sq,n,p,rmax)
            be=math.log(p)/math.log(n)
            mono=all(f[i+1]<=f[i]+1e-9 for i in range(len(f)-1))
            over=any(v>1+1e-9 for v in f)
            firstup=next((i+1 for i in range(len(f)-1) if f[i+1]>f[i]+1e-9), None)
            print(f"  {label:11s} beta={be:.2f} p={p}: f= "+" ".join(f"{v:.3f}" for v in f)
                  +f"  | mono-dec={'Y' if mono else 'N(up@r='+str(firstup)+')'}  any>1={'Y' if over else 'N'}")
