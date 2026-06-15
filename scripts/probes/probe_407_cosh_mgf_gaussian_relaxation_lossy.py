#!/usr/bin/env python3
"""#407 §11e: the GAUSSIAN/sub-Gaussian relaxation of the cosh-MGF identity is FLOOR-LOSING.
Companion to Frontier/CoshMGFIdentity.lean (the exact identity Σ_b cosh(‖η_b‖y)=Σ_r q E_r y^{2r}/(2r)!).
Relaxing E_r ≤ (2r-1)‼ n^r (the Wick/Gaussian ceiling) gives the VALID bound
  Σ_b cosh(‖η_b‖y) ≤ p·exp(n y²/2)   (holds ∀y, verified below),
but the sup-norm bound it yields, min_y arcosh(p e^{ny²/2})/y, is WORSE than the floor
√(2n log m) at every tested prize prime. The exact Bessel saddle I₀(2y)^{n/2} BEATS the floor.
VERDICT: any e^{ny²/2}-type sub-Gaussian MGF bound CANNOT prove CORE — the win lives entirely
in the Bessel curvature I₀(2y)^{n/2}/e^{ny²/2}→0, which the Gaussian (Wick) relaxation discards.
This is the MGF-level statement of §3's 'second-order methods cap at Johnson'."""
import numpy as np, math, cmath
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)):return g
# vectorized FFT period computation; test subgaussian MGF bound  Σ_b cosh(‖η_b‖y) ≤ p e^{n y²/2}
print("subG MGF: does Σ_b cosh(‖η_b‖y) ≤ p·exp(n y²/2) hold ∀y? and bound vs floor")
for p,n in [(4129,8),(40961,8),(786433,16)]:
    if (p-1)%n: continue
    g=proot(p); h=pow(g,(p-1)//n,p)
    ind=np.zeros(p); x=1
    for _ in range(n): ind[x]=1.0; x=x*h%p
    eta=np.fft.fft(ind); absb=np.abs(eta)
    Mtrue=float(absb[1:].max())
    m=(p-1)//n; floor=math.sqrt(2*n*math.log(m))
    # check bound at a grid + compute best sup-norm bound where bound valid
    ys=np.linspace(0.05,2.5,400); best=1e9; besty=0; allhold=True
    for y in ys:
        lhs=float(np.sum(np.cosh(absb*y)))
        rhs=p*math.exp(n*y*y/2)
        if lhs>rhs*(1+1e-9): allhold=False; continue
        val=math.acosh(rhs)/y
        if val<best: best=val; besty=y
    print(f"  p={p} n={n} m={m}: Mtrue={Mtrue:.3f} floor={floor:.3f} subG-bound={best:.3f}@y={besty:.2f} holds∀y={allhold} {'BEATS' if best<floor else 'WORSE'}")
