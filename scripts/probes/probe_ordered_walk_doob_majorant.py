# probe_ordered_walk_doob_majorant.py (#444) — DIR9, the sharpest surviving frontier object. R(b)=
# sup_k|S_k|, S_k = generator-ordered partial sums of e_p(b x), x in mu_n; R majorizes M=|eta_b|=|S_n|.
# DIR9 is the FIRST campaign object simultaneously (i) a TIGHT majorant of M (R/M=1.0026 at the argmax),
# (ii) provably OFF the b-summation dichotomy (sum_b signedArea = 0 exact), (iii) per-b*, order-dependent.
# DECISIVE TEST (here): C_R/C_M = 1.003/1.008/1.018 at n=16/32/64 — R has essentially the SAME worst-case
# constant as M (ratio slowly GROWING). So R(b*)<=C sqrt(n log p) is the wall in VALUE (ordering buys no
# slack). OPEN (the genuine frontier): does a maximal-inequality / van-der-Corput / Doob PROOF of
# R(b*)<=C sqrt(n log p) exist that the direct char-sum route cannot reach? The value reduces; the
# proof-route is the one surviving niche (per-b*, order-dependent, dichotomy-orthogonal).

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
def subgroup_ordered(p,n):
    # generator-ordered: g0^0, g0^1, ... where g0 generates mu_n
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S  # in generator order
def Rwalk(p,roots,b):
    # R(b) = sup_k |S_k|, S_k = sum_{j<k} e_p(b roots[j]) (ordered partial sums)
    ph=np.exp(2j*np.pi*(np.array([b*x%p for x in roots]))/p)
    S=np.concatenate([[0],np.cumsum(ph)])
    return np.abs(S).max(), abs(S[-1])  # R(b), |eta_b|

print("DIR9 DECISIVE TEST: R(b*)=sup_k|S_k| (ordered-walk max excursion) vs M=|eta_b*|. Does R have a")
print("SMALLER/bounded worst-case constant than M (ordering buys slack), or R/M~1 worst-case (reduces)?")
print("="*72)
def find(target,n):
    p=target-(target%n)+1
    for _ in range(40000):
        if (p-1)%n==0 and is_prime(p): return p
        p+=n
    return None
for mu in (4,5,6):
    n=2**mu; p=find(n**4,n); roots=subgroup_ordered(p,n)
    # worst b for M, and worst b for R
    worstM=0; worstR=0; Rat_atMstar=0
    for b in range(1,p):
        R,M=Rwalk(p,roots,b)
        if M>worstM: worstM=M; Rat_atMstar=R/M
        if R>worstR: worstR=R
    CM=worstM/sqrt(n*log(p/n)); CR=worstR/sqrt(n*log(p/n))
    print(f"n={n:3d} p={p:9d}: worst M={worstM:.2f} (C_M={CM:.3f}); worst R={worstR:.2f} (C_R={CR:.3f}); "
          f"R/M at the M-argmax={Rat_atMstar:.4f}; C_R/C_M={CR/CM:.3f}")
print()
print("READING: C_R/C_M ~ 1 (R only slightly bigger) ⟹ the ordered walk has the SAME worst-case scale as M")
print("⟹ bounding R IS bounding M, ordering buys NO slack ⟹ DIR9 reduces (R(b*)<=C sqrt = the wall). If C_R")
print("were strictly smaller / growing slower, the maximal-function route would have genuine slack.")
