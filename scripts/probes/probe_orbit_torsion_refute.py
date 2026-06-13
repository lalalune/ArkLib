import itertools, math
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def factor(m):
    f={};d=2
    while d*d<=m:
        while m%d==0:f[d]=f.get(d,0)+1;m//=d
        d+=1
    if m>1:f[m]=f.get(m,0)+1
    return f
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return [pow(g,i,p) for i in range(n)],g
def interp_eval(p,xs,ys,X):
    fx=0
    for i in range(len(xs)):
        num=ys[i]%p;den=1
        for l in range(len(xs)):
            if l==i:continue
            num=num*((X-xs[l])%p)%p;den=den*((xs[i]-xs[l])%p)%p
        fx=(fx+num*pow(den,p-2,p))%p
    return fx
def orbits(p,n,k,d,a):
    (H,g)=subgroup(p,n);w=[pow(x,d,p) for x in H]
    scale=pow(g,(p-1-d)%(p-1),p)
    sig=lambda ev:tuple(scale*ev[(j+1)%n]%p for j in range(n))
    L=set()
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]
        if len(set(xs))!=k:continue
        ys=[w[i] for i in sub]
        ev=tuple(interp_eval(p,xs,ys,H[j]) for j in range(n))
        if sum(1 for j in range(n) if ev[j]==w[j])>=a:L.add(ev)
    seen=set();no=0
    for ev in L:
        if ev in seen:continue
        no+=1;c=ev
        while c not in seen:seen.add(c);c=sig(c)
    return len(L),no
# n=16,k=8,a=9. Scan primes, record cofactor (p-1)/16 smoothness vs #orbits
n,k,d,a=16,8,9,9
print(f"n={n} k={k} word=x^{d} a={a} (delta={1-a/n:.3f})")
print(f"{'p':>7} {'cofactor=(p-1)/16':>18} {'cofactor factored':>22} {'list':>5} {'#orb':>5}")
cnt=0;p=2*n+1
mins=[]
while cnt<22 and p<6000:
    if (p-1)%n==0 and is_prime(p):
        cof=(p-1)//n
        L,no=orbits(p,n,k,d,a)
        ff=factor(cof)
        smooth=max(ff.keys()) if ff else 1
        tag=" GENERIC(cof prime)" if (is_prime(cof) or cof==1) else (" smooth" if smooth<=7 else "")
        print(f"{p:>7} {cof:>18} {str(ff):>22} {L:>5} {no:>5}{tag}")
        mins.append((no,is_prime(cof) or cof==1))
        cnt+=1
    p+=1
gen=[no for no,isg in mins if isg]
print(f"\n#orbits at GENERIC primes (cofactor prime): {sorted(set(gen))}  -> min={min(mins,key=lambda x:x[0])[0] if mins else '-'}")
print("Construction guess: Kambire bad count C(s,r) with n=sm; /n = orbit count?")
