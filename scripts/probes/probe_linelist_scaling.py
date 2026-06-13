# Does the affine-line list Λ track the witness mass C(n,a)/q^m, even adversarially?
# This is the clean sufficient statement that would close the supply via the line route.
from itertools import product
from math import comb
import random
def codewords(Fq,n,k,dom):
    return [tuple(sum(cc[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for cc in product(range(Fq),repeat=k)]
def Lambda(cw,n,a,u0,u1,Fq):
    cnt=0
    for c in cw:
        for g in range(Fq):
            if sum(1 for i in range(n) if c[i]==(u0[i]+g*u1[i])%Fq)>=a: cnt+=1; break
    return cnt
random.seed(17)
print(f"{'params':<22}{'witnessMass':>12}{'Λ_random':>10}{'Λ_adv':>8}{'ratio_adv/mass':>16}")
for (Fq,n,k,m) in [(11,8,2,0),(13,8,2,0),(17,8,2,0),(11,10,3,0),(13,9,2,0),(11,9,2,1)]:
    a=k+m+1
    if a>n: continue
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    u1=tuple(pow(dom[i],k,Fq) for i in range(n))
    mass=comb(n,a)/Fq**m
    rnd=sum(Lambda(cw,n,a,tuple(random.randrange(Fq) for _ in range(n)),u1,Fq) for _ in range(20))/20
    best=tuple(random.randrange(Fq) for _ in range(n)); bestL=Lambda(cw,n,a,best,u1,Fq)
    for _ in range(500):
        cand=list(best); cand[random.randrange(n)]=random.randrange(Fq); cand=tuple(cand)
        L=Lambda(cw,n,a,cand,u1,Fq)
        if L>=bestL: best,bestL=cand,L
    print(f"F{Fq} n{n} k{k} m{m} a{a}".ljust(22)+f"{mass:>12.1f}{rnd:>10.1f}{bestL:>8}{bestL/mass:>16.3f}")
