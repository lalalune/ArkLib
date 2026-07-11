#!/usr/bin/env python3
"""
Two adversarial checks on the closure of the skeleton:

(E) THE EQUIVALENCE that makes the verdict 'blocked at known wall':
    Claim: [Anom_r <= n^{2r}/p for all r<=~log p]  <=>  M <= C sqrt(n log p).
    => direction is the skeleton's main reduction (verified sound).
    <= direction (the one that makes it a WALL not just an open lemma): does M<=C sqrt(n log p)
       IMPLY A_r<=C' Wick (hence the anomaly bound up to constants)?
    Test: assume the TRUE M (computed exactly). Is A_r <= poly(r)*Wick with the SAME shape?
    More directly: A_r = (1/p) sum_{b!=0}|eta_b|^{2r} <= (1/p)*(p-1)*M^{2r} ~ M^{2r}.
    With M<=C sqrt(n log p): A_r <= (C sqrt(n log p))^{2r} = C^{2r} (n log p)^r.
    Compare to Wick=(2r-1)!! n^r ~ (2r/e)^r n^r. So A_r<=Wick-shape iff (log p)^r <~ (2r-1)!!,
    i.e. r >~ log p / log(2r). So the sup-norm bound gives A_r<=Wick ONLY for r>~log p.
    => the equivalence holds at the OPTIMAL r but the two are NOT term-by-term equivalent.
    Quantify whether M<=C sqrt(n log p) (true value) reproduces A_r<=O(Wick) at r~log p.

(S6) The STEP-6 even-only bound 2^{r-1}<X^r> vs Wick(n). Recompute from scratch.
    X = |u|^2+|v|^2, u=eta_b(mu_h), v=eta_{zeta b}(mu_h), h=n/2.
    Claim: <X^r>/Wick(n) > 1 at small r (1.21 n=16, 1.39 n=32, beta=4) => per-level moment descent fails.
"""
import cmath, math
from sympy import primitive_root

def doublefact(r):
    d=1.0
    for j in range(1,2*r,2): d*=j
    return d
def wick(n,r): return doublefact(r)*n**r

def setup(n,p):
    for a in range(2,p):
        z=pow(a,(p-1)//n,p)
        if pow(z,n,p)==1 and pow(z,n//2,p)==p-1: break
    mu_half=[pow(z,2*j,p) for j in range(n//2)]
    return z,mu_half
def eta(b,S,p,w): return sum(cmath.exp(w*((b*x)%p)) for x in S)

def Mtrue_and_Ar(n,p,rmax):
    z,mu_half=setup(n,p)
    mu_n=mu_half+[(z*x)%p for x in mu_half]
    w=2j*math.pi/p
    Ar=[0.0]*(rmax+1); M=0.0
    for b in range(1,p):
        e=abs(eta(b,mu_n,p,w))
        if e>M: M=e
        e2=e*e; pw=1.0
        for r in range(1,rmax+1):
            pw*=e2; Ar[r]+=pw
    return M,[Ar[r]/p for r in range(rmax+1)]

print("="*90)
print("(E) Does the TRUE sup-norm M reproduce A_r<=O(Wick)?  And M vs C*sqrt(n log p)?")
print("="*90)
for n,plist in [(8,[4073]),(16,[65537]),(32,[1048609])]:
    for p in plist:
        if (p-1)%n:
            # find nearest
            pass
        rmax=8 if n<=16 else 6
        M,Ar=Mtrue_and_Ar(n,p,rmax)
        beta=math.log(p)/math.log(n)
        C_emp=M/math.sqrt(n*math.log(p))
        print(f"n={n} p={p} beta={beta:.2f}: M={M:.3f}  sqrt(n ln p)={math.sqrt(n*math.log(p)):.3f}  "
              f"M/sqrt(n ln p)={C_emp:.3f}")
        # check A_r vs Wick AND vs (M^{2r}) trivial bound
        for r in range(2,rmax+1):
            W=wick(n,r)
            trivial=M**(2*r)  # (1/p)sum<=((p-1)/p)M^{2r}~M^{2r}
            print(f"     r={r}: A_r/Wick={Ar[r]/W:.3f}   M^2r/(p)/Wick(trivial sup bound)={trivial/p/W:.3e}  "
                  f"  (M^2r vastly overcounts: trivial route useless)")
print()
print("="*90)
print("(S6) even-only per-level bound <X^r>/Wick(n).  X=|u|^2+|v|^2 over mu_{n/2}.")
print("="*90)
for n,plist in [(16,[65537]),(32,[1048609])]:
    for p in plist:
        z,mu_half=setup(n,p)  # mu_half = mu_{n/2}
        w=2j*math.pi/p
        h=n//2
        # X_b = |eta_b(mu_h)|^2 + |eta_{zeta b}(mu_h)|^2  -- but careful: skeleton's u=eta_b(mu_h), v=eta_{zeta b}(mu_h)
        # here mu_half IS mu_{n/2}. zeta = z (order n).
        rmax=6
        avgXr=[0.0]*(rmax+1)
        for b in range(1,p):
            u=eta(b,mu_half,p,w)
            v=eta((z*b)%p,mu_half,p,w)
            X=abs(u)**2+abs(v)**2
            pw=1.0
            for r in range(1,rmax+1):
                pw*=X; avgXr[r]+=pw
        for r in range(2,rmax+1):
            Xr=avgXr[r]/p
            W=wick(n,r)
            # even-only bound is 2^{r-1} <X^r>
            print(f"  n={n} p={p} r={r}: <X^r>={Xr:.1f}  2^(r-1)<X^r>/Wick(n)={2**(r-1)*Xr/W:.3f}  "
                  f"<X^r>/Wick(n)={Xr/W:.3f}")
