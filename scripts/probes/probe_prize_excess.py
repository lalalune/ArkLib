#!/usr/bin/env python3
"""
Measure the MOD-P EXCESS E_r^{(p)} - E_r^inf (honest, before any claim).

E_r^inf (Bessel, C roots of unity) is PROVEN <= (2r-1)!! n^r. The prize needs
the FINITE-p subgroup energy E_r^{(p)} = Sum_b |eta_b|^{2r}/p (mu_n in F_p)
clean to r~log p. Excess = E_r^{(p)} - E_r^inf = mod-p additive coincidences
beyond the exact (C) ones. Question: when is excess=0 (=> E_r^{(p)}=E_r^inf
<= Gaussian, clean), and does it track a threshold in p?

For n=8 (E_r^inf = 168,5120,190120 for r=2,3,4 from Bessel), sweep p (n|p-1)
and compute E_r^{(p)} exactly via Sum_b|eta_b|^{2r}. Report excess and the
ratio E_r^{(p)}/((2r-1)!! n^r). Identify the p-threshold where excess->0.
"""
import cmath, math

def primes_with_order(n, count, lo=20):
    out=[]; c=(lo//n+1)*n+1
    while len(out)<count:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): out.append(c)
        c+=n
    return out
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    raise RuntimeError
def Erp(p,H,r):
    tot=0.0
    for b in range(p):
        s=sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in H)
        tot+=(abs(s)**2)**r
    return tot/p
def df(r):
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v

n=8
Einf={2:168, 3:5120, 4:190120}  # Bessel exact (verified)
print(f"n={n}: E_r^inf (Bessel) = {Einf}; Gaussian (2r-1)!!n^r = "
      f"{ {r: df(r)*n**r for r in (2,3,4)} }")
print("p       | r=2 (excess) | r=3 (excess) | r=4 (excess)  [excess=E^(p)-E^inf]")
for p in primes_with_order(n, 9, lo=30):
    if p > 200000: break
    H=subgroup(p,n); row=[]
    for r in (2,3,4):
        E=Erp(p,H,r); exc=E-Einf[r]
        row.append(f"{E:9.0f}({exc:+.0f})")
    print(f"{p:7d} | "+" | ".join(row))
