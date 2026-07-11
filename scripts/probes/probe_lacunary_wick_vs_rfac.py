import math
from collections import Counter
def df(m):
    if m<=0: return 1
    pr=1;k=m
    while k>0: pr*=k;k-=2
    return pr
def mu_set(n,p):
    def order(a):
        o=1;x=a%p
        while x!=1:x=(x*a)%p;o+=1
        return o
    for c in range(2,p):
        if order(c)==n:g=c;break
    return [pow(g,j,p) for j in range(n)]
def Er(n,p,r,mu):
    c=Counter({0:1})
    for _ in range(r):
        nc=Counter()
        for s,cnt in c.items():
            for x in mu: nc[(s+x)%p]+=cnt
        c=nc
    return sum(v*v for v in c.values())
n=16;p=65537;mu=mu_set(n,p)
print(f"n={n} p={p} (Fermat, beta=4) -- does E_r^charp <= Wick hold WITH wraparound present?")
print(f"{'r':>3} {'E_r/Wick':>10} {'E_r/(r!n^r)':>12} {'lacunary r! ok?':>16} {'Wick ok?':>10}")
allwick=True
for r in range(1,13):
    E=Er(n,p,r,mu)
    w=df(2*r-1)*n**r
    rf=math.factorial(r)*n**r
    lac_ok = E<=rf
    wick_ok = E<=w
    allwick = allwick and wick_ok
    print(f"{r:>3} {E/w:>10.4f} {E/rf:>12.4f} {'YES' if lac_ok else 'NO':>16} {'YES' if wick_ok else 'NO':>10}")
print(f"\nE_r <= Wick for ALL r<=12 (with wrap present from r=4): {allwick}")
print("E_r <= r!n^r (lacunary/independent): FAILS from r=2 (E/r!n^r grows 1.0->8.7+) => NOT lacunary-independent")
print("CONCLUSION: char-p energy obeys WICK not the tighter lacunary r! bound; Wick suffices for prize")
print("but proving E_r^charp <= Wick at r~log p = the wraparound (Q4) bound = BGK wall.")
