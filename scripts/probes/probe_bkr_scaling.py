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
def lowdeg(pts,d,coeffs,p): return [sum(coeffs[t]*pow(pts[i],t,p) for t in range(d+1))%p for i in range(len(pts))]
def worst_list(pts,k,a,p,trials,seed=1):
    n=len(pts); rnd=random.Random(seed); best=0
    for _ in range(trials):
        kind=rnd.random()
        if kind<0.4:                       # degree-a structured word
            w=lowdeg(pts,a,[rnd.randrange(p) for _ in range(a+1)],p)
        elif kind<0.8:                     # BKR-style: merge two deg<k codewords on complementary subsets
            c1=lowdeg(pts,k-1,[rnd.randrange(p) for _ in range(k)],p)
            c2=lowdeg(pts,k-1,[rnd.randrange(p) for _ in range(k)],p)
            mask=[rnd.random()<0.5 for _ in range(n)]
            w=[c1[i] if mask[i] else c2[i] for i in range(n)]
        else:                              # merge several codewords
            cs=[lowdeg(pts,k-1,[rnd.randrange(p) for _ in range(k)],p) for _ in range(4)]
            w=[cs[rnd.randrange(4)][i] for i in range(n)]
        best=max(best,list_at(pts,k,a,w,p))
    return best
print("worst sub-Johnson list (a=k+1):  mu_n  vs  additive-set {0..n-1}  vs  random-set")
for n in [8,16,32]:
    p,g=find_prime_root(n); k=2; a=k+1
    muN=[pow(g,j,p) for j in range(n)]
    add=[i%p for i in range(n)]
    rnd=random.Random(5); rndset=random.sample(range(1,p),n)
    tr=3000 if n<=16 else 1200
    LA=worst_list(muN,k,a,p,tr); LB=worst_list(add,k,a,p,tr); LC=worst_list(rndset,k,a,p,tr)
    print(f" n={n:3d} k={k} a={a} (Johnson~{(k*n)**0.5:.1f}):  mu_n={LA}   additive={LB}   random={LC}")
