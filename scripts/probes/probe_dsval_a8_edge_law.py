#!/usr/bin/env python3
"""
A8 EDGE LAW + LOWER BOUND certification.

From probe_dsval_a8_residual_lb.py the worst-dir incidence I(w) is NON-MONOTONE in w:
  - I(w)=0 for w large (no consistent subset: parallel residual condition empty),
  - I(w) jumps to a small plateau (4 or 8) just above the binding band,
  - I(w) = BIG (40, 3536, ...) at/below the binding band w<=b.
The budget crossing (delta* = sup{delta: worstI<=n}) is exactly the LAST w (largest) at which
worstI<=n, i.e. just before the jump to the big value.  Matches prompt for 3/4 cases:
  n=16 rho=1/4: w_e=7 -> 0.5625 (prompt 0.5625) ; n=16 rho=1/2: w_e=11 -> 0.3125 (0.3125);
  n=8 rho=1/2: w_e=6 -> 0.25 (0.25).  n=8 rho=1/4 prompt 0.375 uses dir (4,7) step3 -- check here.

This probe:
  (A) per-direction I(w) table incl. step-3 dir (4,7) for n=8, to reconcile the 0.375 datum;
  (B) the binding-band big-value B(n,step) = I at w=b for worst step-2 dir, hunt closed form;
  (C) the edge w_e(n,rho) and delta_LB = 1 - w_e/n, and compare to 1-rho-c/log2(n).
EXACT char-0 via float on roots of unity (verified against a6 exact Z[zeta] counts).
"""
import itertools, cmath, math
import numpy as np
from math import comb, gcd
TAU=2*math.pi
def mu(n): return [cmath.exp(1j*TAU*s/n) for s in range(n)]

def consistent_gamma(n,k,a,b,S,roots,tol=1e-7):
    xs=np.array([roots[s] for s in S])
    V=np.column_stack([xs**c for c in range(k)])
    ca=xs**a; cb=xs**b
    Q,_=np.linalg.qr(V)
    ra=ca-Q@(Q.conj().T@ca); rb=cb-Q@(Q.conj().T@cb)
    if np.linalg.norm(rb)<tol: return None
    g=-np.vdot(rb,ra)/np.vdot(rb,rb)
    if np.linalg.norm(ra+g*rb)<tol*max(1.0,np.linalg.norm(ra)): return g
    return None

def I_dir(n,k,a,b,w,roots,tol=1e-7,key=4):
    s=set()
    for S in itertools.combinations(range(n),w):
        g=consistent_gamma(n,k,a,b,S,roots,tol)
        if g is not None and abs(g)>tol:
            s.add(complex(round(g.real,key),round(g.imag,key)))
    return len(s)

def main():
    roots8=mu(8)
    print("=== (A) n=8 k=2 per-direction I(w), reconcile 0.375 datum ===")
    for (a,b) in [(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]:
        row=[]
        for w in range(7,2,-1):
            row.append((w,I_dir(8,2,a,b,w,roots8)))
        print(f"  dir({a},{b}) step={b-a}: "+"  ".join(f"w{w}:{I}" for w,I in row))
    # worst-dir edge: largest w with max over dirs I(w) <= budget=8
    print("\n  worst-dir edge n=8 k=2 budget=8:")
    for w in range(7,2,-1):
        m=max(I_dir(8,2,a,b,w,roots8) for a in range(2,8) for b in range(a+1,8))
        print(f"   w={w} delta={1-w/8:.4f} maxI={m} ok={m<=8}")

    print("\n=== (B) binding-band big value B(n) at worst step-2 dir (n/4, n/4+2), w=b ===")
    for n in [8,16,32]:
        roots=mu(n)
        for rho in [0.25,0.5]:
            k=int(round(rho*n)); a=k; b=k+2
            if b>=n: continue
            w=b
            if n<=16:
                I=I_dir(n,k,a,b,w,roots)
            else:
                # n=32 w=b can be big subset count; sample is infeasible exact, skip exact, mark
                I=None
            print(f"  n={n} rho={rho} k={k} dir({a},{b}) step2 w=b={b}: B={I}")

    print("\n=== (C) edge law: w_e and delta_LB vs 1-rho ===")
    for (n,rho) in [(8,0.25),(8,0.5),(16,0.25),(16,0.5)]:
        k=int(round(rho*n)); roots=mu(n)
        we=None
        for w in range(n-1,k,-1):
            m=max((I_dir(n,k,a,b,w,roots) for a in range(k,n) for b in range(a+1,n)),default=0)
            if m<=n: we=w
            else: break  # first violation from the top = edge
        d=1-we/n
        import math as _m
        guess=1-rho-1.0/_m.log2(n)
        print(f"  n={n} rho={rho}: w_e={we} delta_LB=1-w_e/n={d:.4f}  | 1-rho={1-rho:.4f}  | "
              f"1-rho-1/log2n={guess:.4f}  edge-gap=(1-rho)-d={ (1-rho)-d:.4f} = {((1-rho)-d)*_m.log2(n):.3f}/log2n")
    print("\nDONE")

if __name__=="__main__":
    main()
