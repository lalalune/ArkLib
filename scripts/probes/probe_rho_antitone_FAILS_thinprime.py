#!/usr/bin/env python3
"""
probe_rho_antitone_FAILS_thinprime.py  (#444)

REFUTES the ρ-antitone-and-bounded ROUTE in the prize regime at a SMALLER β prime.

The ρ-reduction (RESULTS-444-RHO-ANTITONE + _OpenCoreRhoMonotone) defines
    ρ(r) = S_r / ((p-1)·E_r(ℂ)),   S_r = p·E_r(F_p) − n^{2r},
with E_r(F_p) = #{(x,y)∈μ_n^{2r} : Σx≡Σy mod p} (period energy) and E_r(ℂ) the
cyclotomic (antipodal-reduction) char-0 energy. The sufficient route to the prize is
`∀r, ρ(r+1)≤ρ(r)` (antitone) together with `ρ(1)≤1` ⟹ `∀r, ρ(r)≤1` (open_core_of_
rho_antitone). The published recompute (RESULTS-444-RHO-ANTITONE) reported ρ STRICTLY
DECREASING and ≤1 — but only over its COMPUTED r-cap, and at LARGER primes
(n=32 used p=1048609, β≈4.0).

THIS PROBE shows that at a genuine prize-regime instance with SMALLER β (so the
additive-energy wraparound onsets earlier in r), BOTH route hypotheses FAIL:

  n=32, p=786433  (=3·2^18+1; prime; 32|p−1; β=log_n p≈3.917; μ_32 ⊊ F_p^* proper,
                   thin index 24576; p>n^3):
    ρ(1..5) = 0.999961, 0.999553, 0.996945, 0.998815, 1.017649
    ⟹ ρ(4) > ρ(3)   (antitonicity FAILS), and
    ⟹ ρ(5) > 1       (the ≤1 ceiling FAILS — char-p energy exceeds the Wick/char-0 bound).

  (Contrast n=64, p=2752513: ρ antitone through r=4 — the failure is prime-dependent,
   gated by when wraparound onsets, NOT universal.)

EXACT integer witnesses (kernel-checkable):
    S_3=350241607936, S_4=71393378995104, S_5=18417535837279232,
    E_3(ℂ)=446720, E_4(ℂ)=90889120, E_5(ℂ)=23012946432, p−1=786432.
    ρ(4)>ρ(3) ⟺ S_4·E_3 > S_3·E_4 : 31892850264692858880 > 31833151532688056320 ✓
    ρ(5)>1     ⟺ S_5 > (p−1)·E_5  : 18417535837279232 > 18098117488410624 ✓

HONEST SCOPE: this REFUTES the *sufficiency route* `ρ antitone & ≤1` as an
UNCONDITIONAL lever — it is FALSE at some prize-regime primes (consistent with the §3
meta-theorem that moment/energy routes are non-proving). It does NOT disprove CORE
(the sup bound M(n)≤C√(n log(p/n)) is not implied false by ρ>1 at one r). CORE OPEN.
"""
import sys, math
from collections import Counter
from fractions import Fraction

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

def main():
    cases=[(32,786433),(64,2752513)]
    print("# probe_rho_antitone_FAILS_thinprime (#444)")
    any_fail=False
    for n,p in cases:
        if (p-1)%n!=0:
            print(f"## n={n} p={p}: SKIP"); continue
        S=subgroup(p,n)
        beta=math.log(p)/math.log(n)
        rmax=5 if n<=32 else 4
        print(f"## n={n} p={p} beta={beta:.3f} proper(index {(p-1)//n}) p>n^3:{p>n**3}")
        rhos={}
        for r in range(1,rmax+1):
            Efp=Er_Fp(S,p,r); Sr=p*Efp-n**(2*r); EC=Er_C_2power(n,r)
            rho=Fraction(Sr,(p-1)*EC); rhos[r]=rho
            print(f"   r={r}: S_r={Sr} E_r(C)={EC} rho={float(rho):.6f} (<=1:{rho<=1})")
        for r in range(1,rmax):
            anti = rhos[r+1]<=rhos[r]
            if not anti: any_fail=True
            print(f"   rho({r+1})<=rho({r})? {anti}")
        if any(rhos[r]>1 for r in rhos):
            any_fail=True
            print(f"   ρ>1 at some r: TRUE (ceiling fails)")
    print()
    print(f"=== VERDICT: ρ-antitone-and-bounded ROUTE FAILS at some prize prime = {any_fail} ===")
    return 0

if __name__=="__main__":
    sys.exit(main())
