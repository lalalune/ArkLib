# The genuine frontier: how large can the affine-LINE list Λ be for adversarial u₀?
# Λ(u₀) = #{codewords c : ∃γ, agreement(c, u₀+γ·xᵏ) ≥ a}. u₁=xᵏ fixed (far).
# Compare random u₀ vs structured u₀ vs hill-climbed adversarial u₀.
from itertools import product
import random
def codewords(Fq,n,k,dom):
    return [tuple(sum(cc[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for cc in product(range(Fq),repeat=k)]
def Lambda(cw,n,a,u0,u1,Fq):
    cnt=0
    for c in cw:
        near=False
        for g in range(Fq):
            ag=sum(1 for i in range(n) if c[i]==(u0[i]+g*u1[i])%Fq)
            if ag>=a: near=True; break
        if near: cnt+=1
    return cnt
random.seed(13)
for (Fq,n,k) in [(11,8,2),(11,10,3),(13,7,2)]:
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    u1=tuple(pow(dom[i],k,Fq) for i in range(n))
    for m in range(0,2):
        a=k+m+1
        if a>n: continue
        # random u0 baseline
        rnd=max(Lambda(cw,n,a,tuple(random.randrange(Fq) for _ in range(n)),u1,Fq) for _ in range(30))
        # structured u0 = deg-(k+m) poly eval (should give coherence-count Λ)
        gc=tuple(random.randrange(Fq) for _ in range(k+m+1))
        u0s=tuple(sum(gc[j]*pow(dom[i],j,Fq) for j in range(k+m+1))%Fq for i in range(n))
        stru=Lambda(cw,n,a,u0s,u1,Fq)
        # hill-climb adversarial u0 to maximize Λ
        best=tuple(random.randrange(Fq) for _ in range(n)); bestL=Lambda(cw,n,a,best,u1,Fq)
        for _ in range(400):
            cand=list(best); cand[random.randrange(n)]=random.randrange(Fq); cand=tuple(cand)
            L=Lambda(cw,n,a,cand,u1,Fq)
            if L>=bestL: best,bestL=cand,L
        print(f"F{Fq} n{n} k{k} m{m} a{a}: random Λ≤{rnd}, structured Λ={stru}, "
              f"adversarial Λ≈{bestL}  (|code|=q^k={Fq**k})")
