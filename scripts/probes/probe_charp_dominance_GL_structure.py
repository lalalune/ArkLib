#!/usr/bin/env python3
"""
!!! WARNING (2026-06-20): THIS PROBE USES THE FLAWED naive-integer-lift E_r(C) !!!
Its E_C is wrong at r>=4 (same bug corrected in probe_charp_wraparound_logconcave_Q_v2.py).
Consequently its reported "dominance 0<=G0+L FAILS" cases (n=32/p=786433/r=3, n=64/r=2 with
spurious G0<0) are NOT RELIABLE — G0 is PROVEN >=0 char-0, so a negative G0 here is a probe
artifact, not a real refutation. The DOMINANCE rung 0<=G0+L remains OPEN and UNDETERMINED; it
must be re-probed with the correct antipodal E_r(C) before any conclusion. Kept only as a record
of the structural decomposition tested; DO NOT cite its verdict. TODO: rebuild with Er_C_2power.

probe_charp_dominance_GL_structure.py  (#444, door-iv Lane-2 char-p transfer)

The SECOND open input of `charP_transfer_of_dominance` (after Q>=0 was discharged):
the DOMINANCE inequality
    0 <= G0 + L,
    G0 = gap s a0 b0 c0 = (s+2) b0^2 - s a0 c0   (char-0 gap, PROVEN >=0),
    L  = 2(s+2) b0 wb - s (a0 wc + c0 wa)         (linear-in-W perturbation),
with a0=E_r(C), b0=E_{r+1}(C), c0=E_{r+2}(C) the char-0 energies and
wa=W_r, wb=W_{r+1}, wc=W_{r+2} >= 0 the wraparound excesses.

Machine lore (the file comment): L<0 but |L|<=G0 with growing margin. We test
SUFFICIENT structural conditions that would let the kernel discharge 0<=G0+L
WITHOUT a blind assumption, e.g.:

  (S1) a CLEAN bound  s*(a0 wc + c0 wa) <= 2(s+2) b0 wb + G0   (i.e. just 0<=G0+L);
  (S2) a SHARPER sufficient split: is the negative part s*(a0 wc + c0 wa) itself
       <= G0 alone (so even dropping the positive 2(s+2)b0 wb term, dominance holds)?
       -> if YES, dominance reduces to s*(a0 wc + c0 wa) <= G0, a cleaner inequality.
  (S3) the relative wraparound smallness  W_r / E_r(C)  (how thin the wraparound is).

We compute everything EXACTLY over prize-regime primes and report which sufficient
condition holds, to guide an HONEST formalization (probe-first; nothing larped).
"""
import sys
from collections import defaultdict

def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    facs=list(factorize(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs): return g
    raise RuntimeError("no primroot")

def mu(p,n):
    assert (p-1)%n==0
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def conv_mod(a,b,p):
    o=defaultdict(int)
    for t1,c1 in a.items():
        for t2,c2 in b.items(): o[(t1+t2)%p]+=c1*c2
    return o

def conv_Z(a,b):
    o=defaultdict(int)
    for t1,c1 in a.items():
        for t2,c2 in b.items(): o[t1+t2]+=c1*c2
    return o

def E_Fp(S,p,r):
    base=defaultdict(int)
    for s in S: base[s%p]+=1
    a=dict(base)
    for _ in range(r-1): a=conv_mod(a,base,p)
    return sum(c*c for c in a.values())

def E_C(S,r):
    base=defaultdict(int)
    for s in S: base[s]+=1
    a=dict(base)
    for _ in range(r-1): a=conv_Z(a,base)
    return sum(c*c for c in a.values())

def gap(s,a,b,c): return (s+2)*b*b - s*a*c

def main():
    cases=[(16,65537),(16,40961),(32,1048609),(32,786433),(64,2752513)]
    print("# probe_charp_dominance_GL_structure (#444)")
    print("# test 0<=G0+L and sharper sufficient conditions for the dominance rung")
    allS1=True; allS2=True
    for n,p in cases:
        if (p-1)%n!=0:
            print(f"## n={n} p={p}: SKIP"); continue
        S=mu(p,n)
        rmax=5 if n<=16 else (5 if n==32 else 4)
        EC={}; EW={}
        for r in range(1,rmax+1):
            ec=E_C(S,r); efp=E_Fp(S,p,r)
            EC[r]=ec; EW[r]=efp-ec
        print(f"## n={n} p={p} rmax={rmax}")
        for r in range(1,rmax-1):
            s=2*r+1
            a0,b0,c0=EC[r],EC[r+1],EC[r+2]
            wa,wb,wc=EW[r],EW[r+1],EW[r+2]
            G0=gap(s,a0,b0,c0)
            L = 2*(s+2)*b0*wb - s*(a0*wc + c0*wa)
            neg = s*(a0*wc + c0*wa)   # the negative part of L
            pos = 2*(s+2)*b0*wb       # the positive part of L
            domS1 = (G0 + L >= 0)
            # S2: even dropping the positive term, neg <= G0 ?
            domS2 = (neg <= G0)
            allS1 = allS1 and domS1
            allS2 = allS2 and domS2
            relw = (EW[r+1]/EC[r+1]) if EC[r+1] else 0.0
            print(f"   r={r} s={s}: G0={G0} L={L} G0+L={G0+L} [{'dom' if domS1 else 'FAIL'}]  "
                  f"neg={neg} pos={pos}  neg<=G0:{domS2}  W_{r+1}/E_{r+1}(C)={relw:.4g}")
    print()
    print(f"=== VERDICT: 0<=G0+L everywhere = {allS1} ;  sharper neg<=G0 everywhere = {allS2} ===")
    if allS2:
        print("SHARPER: dominance reduces to s*(a0*wc+c0*wa) <= G0 (drop the positive 2(s+2)b0 wb term).")
    elif allS1:
        print("dominance holds but needs the positive 2(s+2)b0 wb term (neg>G0 somewhere).")
    return 0

if __name__=="__main__":
    sys.exit(main())
