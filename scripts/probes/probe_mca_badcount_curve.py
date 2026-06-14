import itertools
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n: return [pow(g,i,p) for i in range(n)]
def polymod(c,m,p):
    c=c[:]; dm=len(m)-1
    for i in range(len(c)-1,dm-1,-1):
        if c[i]:
            f=c[i]
            for j in range(dm+1): c[i-dm+j]=(c[i-dm+j]-f*m[j])%p
    return c[:dm]
def m_of_T(T,p):
    poly=[1]
    for r in T:
        new=[0]*(len(poly)+1)
        for i,cc in enumerate(poly):
            new[i]=(new[i]+cc*(-r))%p; new[i+1]=(new[i+1]+cc)%p
        poly=new
    return poly
def bad_count(p,H,a,b,k,t):
    n=len(H); res=set()
    for sub in itertools.combinations(range(n),t):
        T=[H[i] for i in sub]
        m=m_of_T(T,p)
        ra=polymod([0]*a+[1],m,p); rb=polymod([0]*b+[1],m,p)
        gamma=None; ok=True
        for j in range(k,t):
            A=ra[j] if j<len(ra) else 0; B=rb[j] if j<len(rb) else 0
            if B==0:
                if A: ok=False;break
            else:
                g=(-A*pow(B,p-2,p))%p
                if gamma is None: gamma=g
                elif gamma!=g: ok=False;break
        if ok and gamma not in (None,0): res.add(gamma)
    return len(res)
n=16;k=8;p=find_prime(n,4000);H=subgroup(p,n)
print(f"n={n} k={k} ρ=0.5 p={p}: MAX #bad over all directions (a,b), per band t")
print(f"{'t':>3} {'δ':>6} {'max#bad':>8} {'worst dir':>10}")
for t in range(k+1, n+1):
    best=0;bd=None
    for a in range(k, n):
        for b in range(a+1, n):
            bc=bad_count(p,H,a,b,k,t)
            if bc>best: best=bc;bd=(a,b)
    print(f"{t:>3} {1-t/n:>6.3f} {best:>8} {str(bd):>10}", flush=True)
