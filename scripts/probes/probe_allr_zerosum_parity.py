import itertools
def mu_n(p,n):
    def is_prim(g):
        x=1; seen=set()
        for _ in range(p-1):
            x=x*g%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_prim(g): g+=1
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    return sorted(set(S))
def zsc(S,r,p):
    c=0
    for t in itertools.product(S,repeat=r):
        if sum(t)%p==0: c+=1
    return c
print("p   n  r  W   even?  negclosed?")
for p,n in [(17,4),(17,8),(41,8),(97,8),(97,16),(193,8)]:
    if (p-1)%n or p-1==n: continue
    S=mu_n(p,n)
    if len(S)!=n: continue
    negclosed = all(((-x)%p) in S for x in S)
    has0 = 0 in S
    for r in [1,2,3,4]:
        if n**r>2_000_000: continue
        W=zsc(S,r,p)
        print(f"{p:3d} {n:2d} {r:2d} {W:8d} {'Y' if W%2==0 else 'N'}  negcl={negclosed} 0inS={has0}")
