#!/usr/bin/env python3
"""
Confirm the BGK cancellation TREND for monomial subgroup sums in the prize
regime: is |S(a,j)|/n -> 0 as n grows (genuine eps>0), and what is eps?

S(a,j) = |sum_{x in mu_n} e_p(a x^j)|. Prize regime p ~ n^beta. Track
max_{a,j} |S| and fit |S| ~ C n^alpha (alpha = 1-eps). If alpha < 1 robustly,
the subgroup-sum cancellation is real and (since the window is Theta(1/log n))
polynomially MORE than enough -- a genuine lead. If alpha -> 1, no usable
cancellation (wall).

Larger n, fixed beta. O(n^2 * samples) per n.
"""
import cmath, math, random

def find_prime_pow(n, beta):
    target=int(n**beta); p=((target)//n+1)*n+1
    while True:
        if p>2 and all(p%d for d in range(2,int(p**0.5)+1)): return p
        p+=n
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    return None
def maxS(p,H,kmax,asamp):
    n=len(H); rng=random.Random(7); best=0.0; argj=0
    for j in range(1,kmax+1):
        Hj=[pow(x,j,p) for x in H]
        for _ in range(asamp):
            a=rng.randrange(1,p)
            s=sum(cmath.exp(2j*math.pi*((a*y)%p)/p) for y in Hj)
            if abs(s)>best: best=abs(s); argj=j
    return best,argj

beta=2.2
print(f"beta={beta}: track |S|/n and fitted exponent alpha (|S|~n^alpha)")
data=[]
for n in (16,32,64,128,256,512):
    p=find_prime_pow(n,beta); H=subgroup(p,n)
    if H is None: 
        # find next prime with n|p-1 above n^beta (already does); subgroup should exist
        print(f"n={n}: no subgroup at p={p}"); continue
    asamp = 300 if n<=128 else 120
    S,j=maxS(p,H,4,asamp)
    data.append((n,S))
    print(f"  n={n:4d} p={p:9d} sqrt(p)={math.sqrt(p):8.1f}  maxS={S:8.2f} (j={j})  "
          f"|S|/n={S/n:.4f}  |S|/sqrt(n)={S/math.sqrt(n):.3f}")
# fit alpha via last-vs-first log-log
if len(data)>=2:
    (n0,S0),(n1,S1)=data[0],data[-1]
    alpha=math.log(S1/S0)/math.log(n1/n0)
    print(f"fitted alpha (|S|~n^alpha) over n={n0}..{n1}: alpha={alpha:.3f}  "
          f"=> eps={1-alpha:.3f}  {'REAL cancellation (eps>0)' if alpha<0.97 else 'NO usable cancellation'}")
    print(f"(compare: sqrt cancellation alpha=0.5; trivial alpha=1; window needs only ~1/log n)")
