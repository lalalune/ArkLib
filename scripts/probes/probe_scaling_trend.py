# Prize-scaled bad-prime trend: worst Excess(ln p)/Wick over a band of primes p ~ n^beta
# (small-subgroup/prize-like), as n grows. Grows => route fails at scale; shrinks => generic.
import math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def gmu(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def Er(roots,p,r):
    f=[0]*p
    for x in roots: f[x]+=1
    for _ in range(r-1):
        nf=[0]*p
        for t in range(p):
            ft=f[t]
            if ft:
                for x in roots: nf[(t+x)%p]+=ft
        f=nf
    return sum(v*v for v in f)
def dblfact(m):
    x=1
    while m>0: x*=m; m-=2
    return x
beta=2.5
print(f"Prize-scaled trend: p ~ n^{beta} (small subgroup). worst Excess(ln p)/Wick over a band.",flush=True)
for n in [16,32,64,128]:
    target=int(n**beta)
    # take up to 6 primes p=1 mod n near target (band [target, target+ ~ ])
    ps=[]; p=target - (target%n) +1
    while len(ps)<6 and p < target*3:
        if isprime(p): ps.append(p)
        p+=n
    worst=0; worstp=0; nbad=0; ratios=[]
    for p in ps:
        r=max(2,round(math.log(p)))
        E=Er(gmu(p,n),p,r)
        ratio=(E-(n**(2*r))/p)/(dblfact(2*r-1)*(n**r))
        ratios.append(round(ratio,3))
        if ratio>1.0: nbad+=1
        if ratio>worst: worst=ratio; worstp=p
    print(f"n={n:<4} p~{target:<7} r~{max(2,round(math.log(target)))}  worst={worst:.3f}@{worstp}  bad={nbad}/{len(ps)}  ratios={ratios}",flush=True)
