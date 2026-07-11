#!/usr/bin/env python3
"""
A8: closed form of the binding-band incidence and the LOWER-BOUND edge law.

Observed (exact char-0):
  The worst-dir incidence I(w) for RS[k] on mu_n has a NON-MONOTONE profile in w:
  zero for w large, a small plateau (4 or 8), then a JUMP to a BIG value at/below the
  binding band w=b.  The budget=n crossing (=> delta* = sup{delta: maxI<=n}) is the largest
  delta (smallest w) at which maxI<=n, i.e. the w just before the jump above n.

THE RECURRING BIG VALUE IS 40 (n=8: dir(6,7) w=3; n=16: dir(4,6)/(8,10) w=b=6/10).
This probe pins:
  (1) the value at the "consecutive-pair top direction" (a,b)=(n-2,n-1), step1, w=k+1
      (the smallest consistent subsets: k+1 points where a (k+2)-genVander is rank-deficient).
      For w=k+1 EVERY (k+1)-subset is consistent (any k+1 points: the (k+1)x(k+2) matrix
      [1..x^{k-1},x^a,x^b] always has a nonzero kernel giving a unique gamma unless degenerate).
      So Cons(k+1) = C(n,k+1) and I(k+1) = #distinct gamma.  THIS is where the 40/3536 come from.
  (2) test I(k+1) and Cons(k+1) closed forms; and the EDGE w_e = smallest w with maxI<=n.

Structural lower-bound claim to certify:
  For w >= w_e, maxI(w) <= n.  Because consistent w-subsets require r_a(S) || r_b(S) in the
  (w-k)-dim residual space -- codim (w-k-1) condition -- so as w grows the consistent family
  collapses to UNIONS of few dilation cosets, and #distinct gamma <= n.

EXACT char-0 (float on roots, verified vs Z[zeta] a6 counts).  Honesty: proper subgroup.
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
    return len(s),  # tuple to also get cons if needed

def I_and_cons(n,k,a,b,w,roots,tol=1e-7,key=4):
    gs=[]
    for S in itertools.combinations(range(n),w):
        g=consistent_gamma(n,k,a,b,S,roots,tol)
        if g is not None and abs(g)>tol:
            gs.append(complex(round(g.real,key),round(g.imag,key)))
    return len(set(gs)),len(gs)

def main():
    print("=== smallest-subset band w=k+1, top consecutive dir (n-2,n-1): the BIG value ===")
    print("    Cons(k+1)=C(n,k+1)?  I(k+1)=?  (this is the budget-busting incidence)")
    rows=[]
    for (n,rho) in [(8,0.25),(8,0.5),(16,0.25),(16,0.5),(32,0.25)]:
        k=int(round(rho*n)); roots=mu(n)
        a,b=n-2,n-1; w=k+1
        # n=32,k=9,w=10 -> C(32,10)=64M too big. cap.
        if comb(n,w)>2_000_000:
            print(f"  n={n} rho={rho} k={k} dir({a},{b}) w={w}: C(n,w)={comb(n,w)} TOO BIG -> skip exact")
            continue
        I,cons=I_and_cons(n,k,a,b,w,roots)
        print(f"  n={n} rho={rho} k={k} dir({a},{b}) w={w}: Cons={cons} (C(n,w)={comb(n,w)})  I={I}"
              f"  I/Cons={I/cons:.3f}  I vs n*(n-1)/2={n*(n-1)//2}  I vs C(n,2)-?")
        rows.append((n,k,I,cons))
    print("\n  hypothesis checks for I(k+1) at dir(n-2,n-1):")
    for (n,k,I,cons) in rows:
        print(f"   n={n} k={k}: I={I} | C(n,2)={comb(n,2)} | n(n-2)/?={n*(n-2)} | "
              f"3n(n-?)... | C(n-k,2)*?  | n^2/? ratios: I/n^2={I/n**2:.4f}")

    print("\n=== EDGE: largest delta (smallest w) with worst-dir maxI<=n; restrict to cheap dirs ===")
    # worst dir at the edge is consistently a step-1 or step-2 dir near the binding band.
    for (n,rho) in [(8,0.25),(8,0.5),(16,0.25),(16,0.5)]:
        k=int(round(rho*n)); roots=mu(n)
        we=None; jump=None
        for w in range(n-1,k,-1):
            m=0
            for a in range(k,n):
                for b in range(a+1,n):
                    Iv,_=I_and_cons(n,k,a,b,w,roots)
                    if Iv>m: m=Iv
            if m<=n: we=w
            else: jump=(w,m); break
        d=1-we/n
        print(f"  n={n} rho={rho}: w_e={we} delta_LB={d:.4f}  jump at w={jump[0]} to maxI={jump[1]}  "
              f"(1-rho={1-rho:.4f}, gap*log2n={((1-rho)-d)*math.log2(n):.3f})")
    print("\nDONE")

if __name__=="__main__":
    main()
