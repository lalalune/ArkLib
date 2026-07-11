"""
Attack cross_r <= 2r n E_r via ENERGY identities (no O(p^2) convolution):
  cross_r = E_{r+1} - n E_r.
  Cauchy-Schwarz: cross_r = sum_{t!=0} N_r(t) c_2(t) <= sqrt(sum_{t!=0}N_r^2) sqrt(sum_{t!=0}c_2^2).
  KEY IDENTITIES:  sum_t N_r(t)^2 = E_{2r};  sum_t c_2(t)^2 = E_2 (additive energy of mu_n).
  => S2 = sqrt(E_{2r}-E_r^2) * sqrt(E_2 - n^2).  Does S2 <= 2r n E_r ? (a PROOF path if yes)
Compute via convolution to depth 2r (feasible).
"""
from collections import Counter
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def energies(p,n,R):
    S=subgroup(p,n); c=Counter({0:1}); E={}
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc
        E[r]=sum(m*m for m in c.values())
    return E,S
n=16; R=16
p=70001
while not(p%n==1 and isprime(p)): p+=1
E,S=energies(p,n,R)
E2=E[2]
# c_2 max:
c2=Counter()
for a in S:
    for b in S: c2[(b-a)%p]+=1
maxc2=max(v for t,v in c2.items() if t!=0)
print(f"n={n} p={p}: E_2={E2}, max_{{t!=0}}c_2={maxc2}, sum_{{t!=0}}c_2^2=E_2-n^2={E2-n*n}")
print(f"  {'r':>2} {'cross_r':>14} {'target=2rnE_r':>14} {'S4 ratio':>8} {'S2(CauchySchwarz)/target':>22}")
for r in range(2,8):
    cross=E[r+1]-n*E[r]
    target=2*r*n*E[r]
    S2=math.sqrt(max(0,E[2*r]-E[r]**2))*math.sqrt(E2-n*n)
    print(f"  {r:>2} {cross:>14} {target:>14} {cross/target:>8.3f} {S2/target:>22.2f}")
print()
print("READING: S4<1 => step-ratio holds (the truth). If S2/target<=1 for all r, Cauchy-Schwarz PROVES it.")
print("  (S2 uses only E_2, E_r, E_{2r} -- all char-0-boundable; a clean reduction if S2 works.)")
