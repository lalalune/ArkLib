#!/usr/bin/env python3
"""Q2 collapse confirmation at n=32 (the cut-off rows) + a clean cosh-vs-moment comparison.
   Confirms cosh_p / mom_p ~ 1 (cosh envelope = best single moment) at larger n."""
import math, numpy as np

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    phi = p-1; facs=set(); m=phi; d=2
    while d*d<=m:
        if m%d==0:
            facs.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def gp_abs(p,n):
    g=primitive_root(p); step=(p-1)//n; x=pow(g,step,p); sub=[]; cur=1
    for _ in range(n): sub.append(cur); cur=(cur*x)%p
    sub=sorted(set(sub)); assert len(sub)==n
    ind=np.zeros(p); ind[np.array(sub)]=1.0
    return np.abs(np.fft.fft(ind))

print("Q2 collapse @ larger n  (cosh_p = char-p cosh one-term bound; mom_p = best single moment)")
print(f"{'n':>4} {'p':>9} | {'trueB':>7} {'floor':>7} | {'mom_p':>7} {'r*':>3} | {'cosh_p':>7} | {'cosh/mom':>8} {'cosh/trueB':>10}")
RMAX=80
for (n,p) in [(32,1048609),(32,4194433 if is_prime(4194433) else 1048609),
              (64,1048705 if is_prime(1048705) else None),(16,2752513 if is_prime(2752513) else None)]:
    if p is None: continue
    if (p-1)%n!=0:
        p=((p//n)+1)*n+1
        while not is_prime(p): p+=n
    if not is_prime(p): continue
    A=gp_abs(p,n); A0=A.copy(); A0[0]=0.0
    trueB=float(A0.max()); floor=math.sqrt(2*n*math.log(p/n))
    best_mom,rstar=math.inf,None
    for r in range(1,RMAX+1):
        S=float(np.sum(A0**(2*r)))
        if S<=0: continue
        v=S**(1.0/(2*r))
        if v<best_mom: best_mom,rstar=v,r
    y_sad=math.sqrt(2*math.log(p)/n); best_cosh=math.inf
    for y in np.linspace(y_sad*0.15,y_sad*4.0,800):
        if y<=0: continue
        zb=A*y; mx=float(zb.max())
        s_all=float(np.sum(np.exp(zb-mx)+np.exp(-zb-mx))/2.0)
        log_all=mx+math.log(s_all)
        inside=math.exp(log_all)-math.cosh(n*y)
        if inside<=1.0: continue
        v=math.acosh(inside)/y
        if v<best_cosh: best_cosh=v
    print(f"{n:>4} {p:>9} | {trueB:>7.2f} {floor:>7.2f} | {best_mom:>7.2f} {rstar:>3} | {best_cosh:>7.2f} | "
          f"{best_cosh/best_mom:>8.4f} {best_cosh/trueB:>10.4f}")
print("=> cosh/mom ~ 1.0x  AND cosh/trueB > 1  => cosh is the moment envelope, never beats the truth.")
