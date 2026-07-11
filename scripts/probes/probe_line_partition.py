from itertools import product, combinations
def codewords(Fq,n,k,dom):
    return [tuple(sum(c[j]*pow(dom[i],j,Fq) for j in range(k))%Fq for i in range(n))
            for c in product(range(Fq),repeat=k)]
def maxag(cw,n,u): return max(sum(1 for i in range(n) if c[i]==u[i]) for c in cw)
def cores(cw,n,a,w):
    s=set()
    for c in cw:
        ag=tuple(i for i in range(n) if c[i]==w[i])
        if len(ag)>=a:
            for T in combinations(ag,a): s.add(T)
    return s
import random; random.seed(5)
ok=True; checked=0
for (Fq,n,k) in [(5,5,2),(7,6,2),(7,7,3),(11,7,2)]:
    dom=list(range(1,n+1)); cw=codewords(Fq,n,k,dom)
    for m in range(0,2):
        a=k+m+1
        if a>n: continue
        # sample far u1's
        far=[]
        for _ in range(2000):
            u1=tuple(random.randrange(Fq) for _ in range(n))
            if maxag(cw,n,u1)<a: far.append(u1)
            if len(far)>=8: break
        for u1 in far:
            for _ in range(3):
                u0=tuple(random.randrange(Fq) for _ in range(n))
                c2s={}
                for g in range(Fq):
                    w=tuple((u0[i]+g*u1[i])%Fq for i in range(n))
                    for T in cores(cw,n,a,w): c2s.setdefault(T,set()).add(g)
                checked+=1
                if any(len(v)>1 for v in c2s.values()):
                    ok=False; print(f"VIOLATION F{Fq} n{n} k{k} m{m}"); break
            if not ok: break
        if not ok: break
    if not ok: break
print(f"LINE-PARTITION (u₁ far ⟹ each core ≤1 scalar): {ok} ({checked} configs)")
