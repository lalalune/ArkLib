import itertools, random
def find_prime_root(n):
    p=n*n
    while True:
        p+=1
        if all(p%d for d in range(2,int(p**0.5)+1)) and (p-1)%n==0:
            for g in range(2,p):
                if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return p,g
def list_at(pts,k,a,w,p):
    n=len(pts); cset=set()
    for Tk in itertools.combinations(range(n),k):
        full=[]
        for jx in range(n):
            tot=0
            for idx,i in enumerate(Tk):
                num=1;den=1
                for i2 in Tk:
                    if i2!=i: num=(num*(pts[jx]-pts[i2]))%p; den=(den*(pts[i]-pts[i2]))%p
                tot=(tot+w[i]*num*pow(den,p-2,p))%p
            full.append(tot)
        if sum(1 for jx in range(n) if full[jx]==w[jx])>=a: cset.add(tuple(full))
    return len(cset)
def lowdeg(pts,d,co,p): return [sum(co[t]*pow(pts[i],t,p) for t in range(d+1))%p for i in range(len(pts))]
def worst(pts,k,a,p,trials,seed=3):
    n=len(pts); rnd=random.Random(seed); best=0
    for _ in range(trials):
        r=rnd.random()
        if r<0.5:
            cs=[lowdeg(pts,k-1,[rnd.randrange(p) for _ in range(k)],p) for _ in range(rnd.randint(2,5))]
            w=[cs[rnd.randrange(len(cs))][i] for i in range(n)]
        else:
            w=lowdeg(pts,a,[rnd.randrange(p) for _ in range(a+1)],p)
        best=max(best,list_at(pts,k,a,w,p))
    return best
print("k=3 separation (a=k+1=4), worst over structured words:")
for n in [16,32]:
    p,g=find_prime_root(n); k=3; a=k+1
    muN=[pow(g,j,p) for j in range(n)]; add=[i%p for i in range(n)]
    tr=2500 if n<=16 else 900
    LA=worst(muN,k,a,p,tr); LB=worst(add,k,a,p,tr)
    print(f" n={n} k={k} a={a} (Johnson~{(k*n)**0.5:.1f}): mu_n={LA}  additive={LB}  ratio={LB/max(LA,1):.1f}")
