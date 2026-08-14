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

# For each n: LAST prime where Spur_3 > slack (=45n^2-40n) AND last prime where Spur_3>0 at all.
for a in [2,3,4]:
    n=2**a
    char0=15*n**3-45*n**2+40*n
    slack=45*n**2-40*n
    last_violate=None; last_pos=None
    p=n+1
    bound=2*n**4 if n==16 else 3*n**4
    if n==16: bound=80000
    while p<=bound:
        if sympy.isprime(p) and p>2:
            sub=subgroup_residues(n,p)
            if len(set(sub))==n and p-1!=n:
                spur=e3_count(sub,p)-char0
                if spur>slack: last_violate=p
                if spur>0: last_pos=p
        p+=n
    print(f"n={n}: slack={slack}, n^4={n**4}")
    print(f"   last prime with Spur>slack (route FAILS): {last_violate}  -> /n^? = {math.log(last_violate,n):.3f}, /n^3={last_violate/n**3:.3f}" if last_violate else "   no violations")
    print(f"   last prime with Spur>0 at all: {last_pos} -> log_n={math.log(last_pos,n):.3f}, /n^4={last_pos/n**4:.4f}" if last_pos else "   Spur=0 for all tested")
