# Λ (affine-line list, dim-k code) ≤ #{P: deg≤k, agreement(P,u₀)≥a} (per-word list, dim-(k+1)).
# And the latter ≤ Johnson n²/(a²−nk) when a²>nk. Verify both.
from itertools import product
from math import comb
import random
def codewords(Fq,n,kk,dom):  # deg < kk
    return [tuple(sum(cc[j]*pow(dom[i],j,Fq) for j in range(kk))%Fq for i in range(n))
            for cc in product(range(Fq),repeat=kk)]
def Lambda(cwk,n,a,u0,u1,Fq):
    cnt=0
    for c in cwk:
        for g in range(Fq):
            if sum(1 for i in range(n) if c[i]==(u0[i]+g*u1[i])%Fq)>=a: cnt+=1; break
    return cnt
def perword_list_k1(cwk1,n,a,u0):
    return sum(1 for P in cwk1 if sum(1 for i in range(n) if P[i]==u0[i])>=a)
random.seed(19); ok=True
for (Fq,n,k) in [(11,8,2),(11,9,2),(13,8,2),(11,10,3)]:
    dom=list(range(1,n+1))
    cwk=codewords(Fq,n,k,dom); cwk1=codewords(Fq,n,k+1,dom)
    u1=tuple(pow(dom[i],k,Fq) for i in range(n))
    for m in range(0,3):
        a=k+m+1
        if a>n: continue
        for _ in range(8):
            u0=tuple(random.randrange(Fq) for _ in range(n))
            L=Lambda(cwk,n,a,u0,u1,Fq); Lk1=perword_list_k1(cwk1,n,a,u0)
            if L>Lk1: ok=False; print(f"REFRAME FAIL F{Fq} n{n} k{k} m{m}: Λ={L}>L_{{k+1}}={Lk1}")
            # Johnson check
            if a*a>n*k:
                jb=n*n/(a*a-n*k)
                if Lk1>jb+1e-9: print(f"  JOHNSON note F{Fq} n{n} k{k} m{m}: L_k1={Lk1} vs JB={jb:.1f}")
    print(f"F{Fq} n{n} k{k}: reframe Λ≤L_(k+1) holds so far")
print("REFRAME (Λ ≤ dim-(k+1) per-word list):", ok)
