# Round 5: the STRUCTURED adversary = degree-a polynomial P -> list = subset-symmetric-fn fibers.
# Deepest band a=k+1: list = max fiber of the elementary-symmetric map e_1=sum over (k+1)-subsets
# of mu_n (subset-sum collisions). General a: fibers of (e_1,...,e_{a-k}). Compare to n-a.
import math
from itertools import combinations
def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None:return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None
def esym(S,t,p):
    # elementary symmetric e_1..e_t of the multiset S, mod p
    e=[1]+[0]*t
    for x in S:
        for j in range(min(t,len(e)-1),0,-1):
            e[j]=(e[j]+x*e[j-1])%p
    return tuple(e[1:t+1])
def max_fiber(D,a,k,p):
    # group a-subsets by their top (a-k) elementary symmetric functions; return max group size
    t=a-k
    if t<1: return None
    from collections import Counter
    cnt=Counter()
    for S in combinations(D,a):
        cnt[esym(S,t,p)]+=1
    return max(cnt.values())
def run(p,n,k):
    D=mun(p,n)
    if D is None: print(f"(p={p} n={n} no mu_n)",flush=True);return
    reg="n<=sqrt(p)" if n*n<=p else "n>sqrt(p)"
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} [{reg}] J={J:.2f} C(n,k+1)={math.comb(n,k+1)} vs p={p}",flush=True)
    for a in range(k+1, min(n, math.ceil(J)+2)):
        mf=max_fiber(D,a,k,p)
        ref="  <<<REFUTES maxlist<=n-a!!!" if mf and mf>(n-a) else ""
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} structured-list(maxfiber)={mf} n-a={n-a}{ref}",flush=True)
# n<=sqrt(p) regime, push k=2,3 where C(n,k+1) can exceed p
run(p=73, n=8, k=2)
run(p=101,n=10,k=2)
run(p=151,n=12,k=2)   # sqrt(151)=12.3, n=12; C(12,3)=220 > 151
run(p=257,n=16,k=2)   # n=16=sqrt(257); C(16,3)=560 > 257
run(p=109,n=9, k=3)   # C(9,4)=126 > 109
run(p=197,n=14,k=2)   # C(14,3)=364 > 197
print("===R5DONE===",flush=True)
