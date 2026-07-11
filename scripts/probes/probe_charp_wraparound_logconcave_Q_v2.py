#!/usr/bin/env python3
"""
probe_charp_wraparound_logconcave_Q_v2.py  (#444) — CORRECTED char-0 energy.

v1 (probe_charp_wraparound_logconcave_Q.py) used a NAIVE integer-lift for E_r(C)
which is WRONG at r>=4 (it counts integer-sum coincidences of residue reps, not the
true cyclotomic vanishing-subset-sum count). Confirmed wrong vs RESULTS-444-RHO:
E_4(C) naive=4650240 but correct=4649680.

This version uses the IN-TREE correct `Er_C_2power` (cyclotomic antipodal reduction
in Z^{n/2}) lifted from probe_444_rho_antitone_recompute.py. It recomputes the
wraparound excess W_r = E_r(F_p) - E_r(C) with the CORRECT E_r(C) and re-tests:
  - W_r >= 0 (wraparound is a nonneg excess),
  - wraparound log-concavity  W_r * W_{r+2} <= W_{r+1}^2,
  - the implied Q(r) = (2r+3) W_{r+1}^2 - (2r+1) W_r W_{r+2} >= 0.

Probe-first HONESTY re-validation of the v1 claim.
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
    """mu_n as residues, ordered by generator power: S[a] = h^a, h=g^{(p-1)/n}."""
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
    """Correct cyclotomic E_r(C), n=2^k: z^a -> +e_a (a<n/2) or -e_{a-n/2} (a>=n/2)."""
    half=n//2
    units=[]
    for a in range(n):
        units.append((a,1) if a<half else (a-half,-1))
    c=Counter({tuple([0]*half):1})
    for _ in range(r):
        nc=Counter()
        for v,m in c.items():
            for (idx,s) in units:
                w=list(v); w[idx]+=s; nc[tuple(w)]+=m
        c=nc
    return sum(m*m for m in c.values())

def main():
    cases=[(8,4073),(8,12289),(16,65537),(16,40961),(32,1048609),(32,786433),(64,2752513)]
    print("# probe_charp_wraparound_logconcave_Q_v2  (#444) CORRECT E_r(C)")
    print("# W_r=E_r(F_p)-E_r(C); test W_r*W_{r+2}<=W_{r+1}^2 => Q=(2r+3)W_{r+1}^2-(2r+1)W_r W_{r+2}>=0")
    all_lc=True; all_Q=True; all_nonneg=True
    for n,p in cases:
        if (p-1)%n!=0:
            print(f"## n={n} p={p}: SKIP"); continue
        S=subgroup(p,n)
        rmax=6 if n<=16 else (5 if n==32 else 4)
        W={}; ok=True
        for r in range(1,rmax+1):
            efp=Er_Fp(S,p,r); ec=Er_C_2power(n,r); w=efp-ec; W[r]=w
            if w<0: ok=False
        all_nonneg=all_nonneg and ok
        print(f"## n={n} p={p} rmax={rmax} W_r>=0 all:{ok}")
        for r in range(1,rmax+1):
            print(f"   W_{r}={W[r]}")
        for r in range(1,rmax-1):
            s=2*r+1
            lhs=W[r]*W[r+2]; rhs=W[r+1]**2
            lc=lhs<=rhs
            Q=(s+2)*W[r+1]**2 - s*W[r]*W[r+2]
            all_lc=all_lc and lc; all_Q=all_Q and (Q>=0)
            print(f"   r={r} s={s}: W_r*W_r+2={lhs} W_r+1^2={rhs} [{'LC-ok' if lc else 'LC-FAIL'}] "
                  f"Q={Q} [{'Q>=0' if Q>=0 else 'Q<0!!'}]")
    print()
    print(f"=== VERDICT: W_r>=0 all={all_nonneg} ; wrap log-concavity all={all_lc} ; Q>=0 all={all_Q} ===")
    return 0

if __name__=="__main__":
    sys.exit(main())
