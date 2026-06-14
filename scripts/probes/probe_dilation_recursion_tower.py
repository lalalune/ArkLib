import cmath, math, random
def find_prime_with_subgroup(mu, beta_min=4):
    n = 1<<mu
    target = n**beta_min
    cand = ((target)//n)*n + 1
    for t in range(cand, cand+ n*5000, n):
        if t>2 and all(t%d for d in range(2,int(t**0.5)+1)):
            return n,t
    return n,None
def subgroup_gen(p,n):
    g=2
    while True:
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1:
            return h
        g+=1
for mu in [3,4,5]:
    n,p = find_prime_with_subgroup(mu,4)
    if p is None: continue
    h = subgroup_gen(p,n)
    w=2*math.pi/p
    def emb(x): return cmath.exp(1j*w*(x%p))
    subs=[[pow(h,((n>>i)*j)%n,p) for j in range(1<<i)] for i in range(mu+1)]
    def fi(i,b): return sum(emb(b*x) for x in subs[i])
    okrec=True
    for i in range(mu):
        zeta=pow(h,(n>>(i+1))%n,p)
        for _ in range(15):
            b=random.randrange(1,p)
            if abs(fi(i+1,b)-(fi(i,b)+fi(i,zeta*b)))>1e-6: okrec=False
    L2=[sum(abs(fi(i,b))**2 for b in range(1,p)) for i in range(mu+1)]
    ratios=[round(L2[i+1]/L2[i],3) for i in range(mu)]
    mx=max(abs(fi(mu,b)) for b in range(1,p))
    floor=math.sqrt(n*math.log(p/n))
    print(f"mu={mu} n={n} p={p} beta={math.log(p)/math.log(n):.2f} | rec_ok={okrec} | L2ratios={ratios} | max|f|={mx:.2f} floor={floor:.2f} ratio={mx/floor:.3f}")
