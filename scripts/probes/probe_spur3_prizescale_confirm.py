from collections import defaultdict
import sympy, math
def subgroup_residues(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]
def e3_count(sub,p):
    T3=defaultdict(int)
    for a in sub:
        for b in sub:
            ab=(a+b)%p
            for c in sub: T3[(ab+c)%p]+=1
    return sum(cnt*T3[(-s)%p] for s,cnt in T3.items())
def find_prime(n,beta):
    target=int(round(n**beta)); k0=max(2,target//n)
    for dk in range(0,50000):
        for k in (k0+dk,k0-dk):
            if k>=2:
                p=k*n+1
                if sympy.isprime(p): return p
    return None
# Confirm Spur_3 = 0 at MULTIPLE prize-scale primes per n (beta=4,4.5,5), non-Fermat included
print("PRIZE-SCALE CONFIRMATION: Spur_3(p) at p>=n^4, multiple primes/beta")
for a in [2,3,4]:
    n=2**a
    char0=15*n**3-45*n**2+40*n
    for beta in [4.0,4.5,5.0]:
        p=find_prime(n,beta)
        if not p: continue
        sub=subgroup_residues(n,p)
        if len(set(sub))!=n or p-1==n: continue
        spur=e3_count(sub,p)-char0
        print(f"  n={n:3d} p={p:9d} (p~n^{math.log(p,n):.2f}) Spur_3={spur:+d}  {'OK Spur=0' if spur==0 else 'NONZERO'}")
