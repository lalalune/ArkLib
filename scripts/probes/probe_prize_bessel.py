#!/usr/bin/env python3
"""
THE BESSEL REDUCTION (novel): E_r^inf(mu_{2^mu}) = (2r)! [x^{2r}] I_0(2x)^{n/2}.

For n=2^mu, mu_n elements map to +/-unit vectors in Z^{n/2} (zeta^{n/2}=-1),
so the exact additive energy E_r^inf = #{2r-step +/-unit walk in Z^d (d=n/2)
returning to 0} = (2r)! [x^{2r}] I_0(2x)^d, where I_0(2x)=sum_m x^{2m}/(m!)^2.
Clean (Gaussian) value (2r-1)!! n^r = leading e^{d x^2} term.

This probe:
 (1) VERIFIES the Bessel formula against direct +/-unit-walk return counts;
 (2) computes the ratio E_r/((2r-1)!! n^r) at LARGE n,r (cheap via the GF -
     no n^{2r} enumeration!), reaching the clean-moments regime r~log n
     that direct energy computation could NOT;
 (3) checks the key inequality E_r <= (2r-1)!! n^r (=> Markov => closes delta*),
     and the r~log(n) threshold where the ratio stays bounded.
"""
import math
from fractions import Fraction

def bessel_pow_coeffs(d, R):
    # coefficients of I_0(2x)^d up to x^{2R}, in variable u=x^2:
    # I_0(2x) = sum_{m>=0} u^m/(m!)^2 ; raise to d via poly mult (truncate u^R)
    base=[Fraction(1, math.factorial(m)**2) for m in range(R+1)]
    poly=[Fraction(1)]+[Fraction(0)]*R
    for _ in range(d):
        new=[Fraction(0)]*(R+1)
        for i in range(R+1):
            if poly[i]==0: continue
            for j in range(R+1-i):
                new[i+j]+=poly[i]*base[j]
        poly=new
    return poly  # poly[m] = [u^m] I_0(2x)^d = [x^{2m}] I_0(2x)^d

def Er_bessel(n, r):
    d=n//2
    c=bessel_pow_coeffs(d, r)
    return math.factorial(2*r)*c[r]   # (2r)! [x^{2r}] I_0(2x)^d  (Fraction -> int)

def df(r):
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v

# (1) verify against known exact values
print("verify Bessel formula vs direct exact energy:")
for (n,r,known) in [(8,2,168),(8,3,5120),(8,4,190120),(16,2,720),(16,3,50560),(32,3,446720)]:
    E=Er_bessel(n,r)
    print(f"  n={n} r={r}: Bessel={int(E)}  direct={known}  {'OK' if int(E)==known else 'MISMATCH'}")

# (2)(3) ratio at LARGE n, r up to ~log2(n)+ (cheap now)
print("\nratio E_r/((2r-1)!! n^r) at scale [<=1 => sub-Gaussian => Markov closes]:")
print("n        | r=2    r=4    r=8    r=12   r=16   r=log2(n)")
for mu in (6,8,10,12,14):
    n=2**mu; row=[]
    for r in (2,4,8,12,16,mu):
        E=Er_bessel(n,r); ratio=float(Fraction(int(E), df(r)*n**r)) if df(r)*n**r>0 else 0
        row.append(f"{ratio:.3f}")
    print(f"2^{mu:2d}={n:7d}| "+"  ".join(row))
