#!/usr/bin/env python3
"""
UVST refutation hunt (#444, 2026-06-19): is the full spectral-flatness UVST ever FALSE
at STRUCTURED primes? And is there an elementary L^4 (additive-energy) saving?

Two tests, both bearing on the workflow's loop2/refutation phase:

(A) STRUCTURED-PRIME STRESS. Fix n=2^a. Sweep primes p ≡ 1 (mod 2n), p>n^4, recording v2(p-1)
    (2-adic valuation) and the normalized sup-norm Sh = M/sqrt(n log(p/n)), M=max_b|eta_b|.
    Memory flags "high-v2(p-1) stratum mean rises toward sqrt2 as n grows." If at FERMAT-like primes
    (v2(p-1) maximal) Sh blows past sqrt2 or grows, UVST(full) would be in danger. If Sh stays
    bounded (<~1.5) across ALL v2 strata, UVST(full) is supported (not refuted) at this scale.

(B) L^4 / ADDITIVE-ENERGY SAVING. The 4th DFT moment (1/m) sum_b |S_b|^4 = (additive energy of the
    phase sequence) and equals 2 m^2 (1+o(1)) for a random sequence (real Wick). Measure the exact
    ratio (1/m sum|S_b|^4)/(2 m^2) and (1/m sum|S_b|^4)/(3 m^2)? For a REAL sequence the 4th moment
    Wick is 3*(2nd)^2 = 3 m^2... we report both and the implied L^4->L^inf gap: M <= (sum|S|^4)^{1/4}
    is the trivial-from-L4 bound; how far above sqrt(m log m) is it? (Quantifies why L^4 alone can't
    give the sup — the L4->Linf gap is a power of m.)
"""
import sys, math
import numpy as np

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def v2(x):
    v=0
    while x%2==0: x//=2; v+=1
    return v

def gen(p):
    pf=set();mm=p-1;d=2
    while d*d<=mm:
        while mm%d==0:pf.add(d);mm//=d
        d+=1
    if mm>1:pf.add(mm)
    g=2
    while any(pow(g,(p-1)//q,p)==1 for q in pf):g+=1
    return g

def supnorm(p,n):
    g=gen(p); m=(p-1)//n
    h=pow(g,m,p)
    mun=np.empty(n,dtype=np.int64);x=1
    for i in range(n):mun[i]=x;x=x*h%p
    reps=np.empty(m,dtype=np.int64);cur=1
    for j in range(m):reps[j]=cur;cur=cur*g%p
    M=0.0; tp=2*math.pi/p; CH=8192
    s4=0.0; s2=0.0
    for s in range(0,m,CH):
        blk=reps[s:s+CH]
        prod=(blk[:,None]*mun[None,:])%p
        eta=np.cos(tp*prod).sum(axis=1)
        a2=eta*eta
        M=max(M, float(np.sqrt(a2.max())))
        s2+=float(a2.sum()); s4+=float((a2*a2).sum())
    return M, s2, s4, m

def testA(n, count=40):
    print(f"=== (A) STRUCTURED-PRIME STRESS  n={n} (Johnson sqrt2={math.sqrt(2):.3f}) ===")
    strata={}
    p = (n*n*n*n)  # start near n^4
    p += (2*n - (p % (2*n))) + 1  # make p ≡ 1 mod 2n
    found=0; maxSh=0.0; argmax=None
    while found<count:
        if isprime(p):
            M,_,_,m = supnorm(p,n)
            sh = M/math.sqrt(n*math.log(p/n))
            vv=v2(p-1)
            strata.setdefault(vv,[]).append(sh)
            if sh>maxSh: maxSh=sh; argmax=(p,vv)
            found+=1
        p += 2*n
    for vv in sorted(strata):
        arr=strata[vv]
        print(f"   v2(p-1)={vv:2d}: n_primes={len(arr):2d}  meanSh={sum(arr)/len(arr):.3f}  maxSh={max(arr):.3f}")
    print(f"   OVERALL maxSh={maxSh:.3f} at p={argmax[0]} (v2={argmax[1]});  {'<1.5 OK (UVST supported)' if maxSh<1.5 else 'WATCH: >1.5'}")
    print()

def testB(n):
    p=(n**4); p += (2*n-(p%(2*n)))+1
    while not isprime(p): p+=2*n
    M,s2,s4,m=supnorm(p,n)
    # S_b = m*eta_b/sqrt p approx (Theorem A, ignoring the -1). Work directly with eta moments.
    # 2nd moment over b!=0: sum_{b!=0} eta^2 = n(p-n); per coset mean eta^2 = (p-n)/... we use coset sums:
    # s2 = sum_cosets eta^2 = (p-n) [since sum_{b!=0}eta^2 = n*s2 = n(p-n)] -> mean eta^2 = s2/m
    mean2=s2/m; mean4=s4/m
    wick4_real=3*mean2*mean2
    print(f"=== (B) L^4 / additive-energy saving  n={n} p={p} m={m} ===")
    print(f"   mean eta^2 = {mean2:.3f} (~n={n});  mean eta^4 = {mean4:.3f}")
    print(f"   real-Wick 3*(mean2)^2 = {wick4_real:.3f}   ratio mean4/Wick4 = {mean4/wick4_real:+.4f}  ({'sub-Gaussian' if mean4<wick4_real else 'super'})")
    # L4->Linf: trivial sup from L4 is (sum_b eta^4)^{1/4} = (m*mean4)^{1/4}
    L4sup=(m*mean4)**0.25
    target=math.sqrt(n*math.log(p/n))
    print(f"   L^4-trivial sup bound (m*mean4)^(1/4) = {L4sup:.3f}  vs target sqrt(n log m)={target:.3f}  (gap factor {L4sup/target:.2f} = a power of m: L4 alone insufficient)")
    print(f"   actual M={M:.3f}  Sh={M/target:.3f}")
    print()

if __name__=='__main__':
    ns=[int(a) for a in sys.argv[1:]] or [16,32]
    for n in ns:
        testA(n, count=30)
        testB(n)
