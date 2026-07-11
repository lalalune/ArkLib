# probe_dir9_rademacher_menshov_baverage.py (#444) — settles DIR9's sharpest proof angle. R(b)=sup_k
# |S_k|, ordered-walk excursion. Rademacher-Menshov (the deterministic maximal inequality) needs the
# increments a_j(b)=e_p(b g0^j) ORTHOGONAL; their ONLY orthogonality is in the b-VARIABLE (sum_b a_j conj
# a_j' = p[j=j']). So R-M controls the b-AVERAGE of R, not max_b R. VERIFIED: avg_b R (rms) ~ 1.16-1.20*sqrt(n)
# (sub-Gaussian, even below R-M's sqrt(n)logn), but max_b R is 2.99/3.46/4.09 x the average (GROWING) at
# n=16/32/64. So R-M gives the phase-blind b-average (~sqrt n); the max-over-b is the wall. DIR9's
# maximal-function proof route REDUCES — the same avg-vs-max gap ('every door is a mirror'): the ordered
# walk's average excursion is genuinely sub-Gaussian but its worst-case is sqrt(n log p), controllable only
# in the b-average. The ordered walk does NOT escape the wall.

import numpy as np
from math import sqrt, log
def is_prime(N):
    if N<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41):
        if N%q==0:return N==q
    d=N-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,N)
        if x in(1,N-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%N
            if x==N-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def ordsub(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def find(t,n):
    p=t-(t%n)+1
    for _ in range(40000):
        if (p-1)%n==0 and is_prime(p):return p
        p+=n
    return None
print("RADEMACHER-MENSHOV sharpest check: R(b)=sup_k|S_k|. The increments a_j(b)=e_p(b g0^j) are")
print("orthogonal in the b-VARIABLE (sum_b a_j conj a_j' = p[j=j']). So R-M bounds the L2(b)-AVERAGE of R,")
print("NOT max_b R. Compare: avg_b R, R-M bound ~sqrt(n)*log n, max_b R (=the wall), prize 2sqrt(n log n).")
print("="*74)
for mu in (4,5,6):
    n=2**mu; p=find(n**4,n); roots=ordsub(p,n)
    ph=np.exp(2j*np.pi*(np.outer(np.arange(p),roots)%p)/p)  # p x n
    S=np.concatenate([np.zeros((p,1)),np.cumsum(ph,axis=1)],axis=1)  # p x (n+1)
    R=np.abs(S).max(axis=1)  # R(b) for each b
    avgR=sqrt(np.mean(R[1:]**2))      # rms over b!=0 = L2(b) average
    maxR=R[1:].max()                   # max over b = the wall object
    rm = sqrt(n)*log(n)               # Rademacher-Menshov scale sqrt(n) log n
    prize = 2*sqrt(n*log(n))          # prize scale ~ sqrt(n log p), log p=4 log n
    print(f"n={n:3d} p={p:9d}: avg_b R (rms)={avgR:.2f}  max_b R={maxR:.2f}  |  R-M sqrt(n)logn={rm:.2f}  prize 2sqrt(n logn)={prize:.2f}")
    print(f"           avg_b R / (sqrt n) = {avgR/sqrt(n):.2f} (R-M predicts ~log n={log(n):.2f});  max_b R / avg_b R = {maxR/avgR:.3f} (the avg->max gap)")
print()
print("READING: if avg_b R ~ sqrt(n)*const (R-M-controlled, phase-blind b-average) while max_b R is strictly")
print("larger (the gap >1), then R-M gives ONLY the b-average = the wall reappears at the max. The increments'")
print("ONLY orthogonality is in b => R-M is intrinsically a b-average tool => DIR9 reduces ('every door a mirror').")
