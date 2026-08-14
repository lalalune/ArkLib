# Verify deep-hole classification x^j, j==k (mod 4) for varying k; and check the deep-hole RESIDUE.
import itertools, math
from sympy import primitive_root, isprime
def setup(n,beta=4):
    p=n**beta
    while not ((p-1)%n==0 and isprime(p)): p+=1
    g=pow(primitive_root(p),(p-1)//n,p); return p,[pow(g,j,p) for j in range(n)]
def maxagree(u,mu,k,p):
    n=len(mu); best=0
    for T in itertools.combinations(range(n),k):
        ag=0
        for xi in range(n):
            x=mu[xi]; val=0
            for i in T:
                num=1;den=1
                for j in T:
                    if i!=j: num=num*((x-mu[j])%p)%p; den=den*((mu[i]-mu[j])%p)%p
                val=(val+u[i]*num*pow(den,p-2,p))%p
            if val==u[xi]: ag+=1
        best=max(best,ag)
    return best
for n in [8,16]:
    p,mu=setup(n)
    print(f"\n=== n={n} p={p}: deep-hole monomial exps by k (predict j == k mod 4) ===")
    for k in [2,3,4,5]:
        if k>=n: continue
        rows=[(j, n-maxagree([pow(mu[i],j,p) for i in range(n)],mu,k,p)) for j in range(n)]
        R=max(d for _,d in rows)
        deep=[j for j,d in rows if d==R]
        pred=[j for j in range(n) if j%4==k%4]
        print(f"  k={k}: R={R} deep={deep}  predict(j==k mod4)={pred}  match={set(deep)==set(j for j in deep if j>=k) and all(j%4==k%4 for j in deep)}")
