# Conjecture L: is the power word EXTREMAL at the middle band for a PROPER 2-power subgroup?
# mu_8 subset F_17 (proper, QR), k=2, t=3.  Strong search (random + hill-climb) for max list,
# compare to power-word list = #{t-subsets summing to 0}.
import itertools, random
random.seed(3)
p=17
# mu_8 = order-8 subgroup of F_17^* = quadratic residues
g=3  # generator of F_17^*
sub=sorted({pow(g,(2*i),p) for i in range(8)})  # <g^2> order 8
n=len(sub); k=2
import math
print(f"mu_8 = {sub}  (n={n}, proper subgroup of F_17^*); k={k}; Johnson agree={math.sqrt(n*k):.2f}, capacity agree={k}")
pw=[[pow(a,j,p) for j in range(k)] for a in sub]
def list_size(w,t):
    cnt=0
    for coeffs in itertools.product(range(p),repeat=k):
        ag=0
        for i in range(n):
            v=0
            for j in range(k): v=(v+coeffs[j]*pw[i][j])%p
            if v==w[i]: ag+=1
        if ag>=t: cnt+=1
    return cnt
def mono(e): return [pow(a,e,p) for a in sub]
def hillclimb(t,iters=200):
    w=[random.randrange(p) for _ in range(n)]
    best=list_size(w,t)
    for _ in range(iters):
        i=random.randrange(n); old=w[i]; improved=False
        for val in range(p):
            if val==old: continue
            w[i]=val; L=list_size(w,t)
            if L>best: best=L; old=val; improved=True
        w[i]=old
    return best
for t in [3]:  # the middle band for n=8,k=2
    Lpow=list_size(mono(t),t)
    # exact power-word interpretation: #{t-subsets of mu_8 summing to 0}
    fib=sum(1 for S in itertools.combinations(sub,t) if sum(S)%p==0)
    Lmon={e:list_size(mono(e),t) for e in [2,3,4,5,7]}
    # strong search
    hc=max(hillclimb(t) for _ in range(15))
    Lr=max(list_size([random.randrange(p) for _ in range(n)],t) for _ in range(300))
    print(f" t={t}: L(x^t)={Lpow} (=#sumzero-{t}-subsets={fib})  monomials={Lmon}")
    print(f"        STRONG max search: hillclimb={hc}, best_of_300_random={Lr}")
    print(f"   -> power word extremal? {'YES' if Lpow>=max(hc,Lr) else 'NO (beaten by '+str(max(hc,Lr))+')'}")
