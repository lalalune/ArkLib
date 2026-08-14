#!/usr/bin/env python3
"""
probe_charp_dominance_GL_v2.py  (#444, door-iv Lane-2 char-p transfer) — CORRECT E_r(C).

Re-probes the SECOND open input of charP_transfer_of_dominance (the first, Q>=0, is
discharged in _CharPWraparoundLogConcaveQ.lean): the DOMINANCE inequality
    0 <= G0 + L,
    G0 = gap s a0 b0 c0 = (s+2) b0^2 - s a0 c0    (char-0 gap, PROVEN >=0 for n>=8),
    L  = 2(s+2) b0 wb - s (a0 wc + c0 wa)          (linear-in-W perturbation),
a0=E_r(C), b0=E_{r+1}(C), c0=E_{r+2}(C) char-0 energies; wa,wb,wc = W_r,W_{r+1},W_{r+2}.

USES THE CORRECT cyclotomic antipodal E_r(C) (Er_C_2power), unlike the flawed v1.

Tests, at every interior r over prize-regime primes:
  (D)  0 <= G0 + L                         (the dominance rung itself)
  (D-strong)  s*(a0 wc + c0 wa) <= G0       (sharper: drop the positive 2(s+2)b0 wb term)
  also reports G0>=0 (sanity, should always hold with correct E_C) and the relative
  wraparound thinness W_{r+1}/E_{r+1}(C).
HONEST: probe-first. If D holds with a clean sufficient form, that's the next formalize
target; if D ever fails, that is itself a constraint result (a real obstruction).
"""
import sys
from collections import Counter

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

def subgroup(p,n):
    assert (p-1)%n==0
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def Er_Fp(S,p,r):
    c=Counter({0:1})
    for _ in range(r):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc
    return sum(m*m for m in c.values())

def Er_C_2power(n,r):
    half=n//2
    units=[(a,1) if a<half else (a-half,-1) for a in range(n)]
    c=Counter({tuple([0]*half):1})
    for _ in range(r):
        nc=Counter()
        for v,m in c.items():
            for (idx,s) in units:
                w=list(v); w[idx]+=s; nc[tuple(w)]+=m
        c=nc
    return sum(m*m for m in c.values())

def gap(s,a,b,c): return (s+2)*b*b - s*a*c

def main():
    cases=[(16,65537),(16,40961),(32,1048609),(32,786433),(64,2752513)]
    print("# probe_charp_dominance_GL_v2 (#444) CORRECT antipodal E_r(C)")
    print("# test 0<=G0+L (dominance) and sharper s(a0 wc + c0 wa)<=G0")
    allD=True; allDs=True; allG0=True
    for n,p in cases:
        if (p-1)%n!=0:
            print(f"## n={n} p={p}: SKIP"); continue
        S=subgroup(p,n)
        rmax=5 if n<=32 else 4
        EC={}; EW={}
        for r in range(1,rmax+1):
            ec=Er_C_2power(n,r); efp=Er_Fp(S,p,r)
            EC[r]=ec; EW[r]=efp-ec
        print(f"## n={n} p={p} rmax={rmax}")
        for r in range(1,rmax-1):
            s=2*r+1
            a0,b0,c0=EC[r],EC[r+1],EC[r+2]
            wa,wb,wc=EW[r],EW[r+1],EW[r+2]
            G0=gap(s,a0,b0,c0)
            L=2*(s+2)*b0*wb - s*(a0*wc + c0*wa)
            neg=s*(a0*wc + c0*wa); pos=2*(s+2)*b0*wb
            D=(G0+L>=0); Ds=(neg<=G0); g0ok=(G0>=0)
            allD=allD and D; allDs=allDs and Ds; allG0=allG0 and g0ok
            relw=(EW[r+1]/EC[r+1]) if EC[r+1] else 0.0
            print(f"   r={r} s={s}: G0={G0}[{'+' if g0ok else 'NEG!'}] L={L} G0+L={G0+L} "
                  f"[{'dom' if D else 'FAIL'}] neg<=G0:{Ds} W/E={relw:.4g}")
    print()
    print(f"=== VERDICT: G0>=0 all={allG0} ; dominance 0<=G0+L all={allD} ; sharper neg<=G0 all={allDs} ===")
    if allDs:
        print("SHARPER sufficient form holds: dominance reduces to s(a0 wc + c0 wa) <= G0.")
    elif allD:
        print("dominance holds but needs the positive 2(s+2)b0 wb term.")
    else:
        print("DOMINANCE FAILS somewhere with CORRECT E_C -> a real obstruction; constraint result.")
    return 0

if __name__=="__main__":
    sys.exit(main())
