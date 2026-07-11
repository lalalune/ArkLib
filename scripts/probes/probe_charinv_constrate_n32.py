import itertools, math
def isp(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True
def proot(p,n):
    for c in range(2,p):
        h=pow(c,(p-1)//n,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    return None
def solve(M,bvec,p):
    m=len(M); A=[row[:]+[bvec[i]] for i,row in enumerate(M)]; r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0: piv=i;break
        if piv is None: return None
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],p-2,p)
        A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c]; A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]
def bandcounts(p,n,k,a,b):
    z=proot(p,n); pts=[pow(z,i,p) for i in range(n)]
    za=[pow(z,(i*a)%n,p) for i in range(n)]; zb=[pow(z,(i*b)%n,p) for i in range(n)]
    # precompute powers pts[i]^j
    powr=[[pow(pts[i],j,p) for j in range(k)] for i in range(n)]
    ga={}
    for A in itertools.combinations(range(n),k+1):
        M=[powr[i]+[(-za[i])%p] for i in A]; rhs=[zb[i] for i in A]
        sol=solve(M,rhs,p)
        if sol is None: continue
        gamma=sol[k]
        if gamma in ga: continue
        g=sol[:k]; cnt=0
        for i in range(n):
            gi=0; xi=pts[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(zb[i]+gamma*za[i])%p: cnt+=1
        ga[gamma]=cnt
    return {w:sum(1 for v in ga.values() if v>=w) for w in range(k+1,n+1)}
n,k=32,4   # rho=1/8; window (1-sqrt(1/8),1-1/8)=(0.646,0.875) -> w in (4, 11)
primes=[p for p in [1153,40961,65537,557057,1179649] if isp(p) and (p-1)%n==0]
print(f"n={n} k={k} rho={k/n}=1/8, n^3={n**3}, primes={primes}")
for (a,b) in [(5,6),(5,7),(9,13)]:
    print(f"pencil({a},{b}) gcd={math.gcd(b-a,n)}:")
    prof={}
    for p in primes:
        bc=bandcounts(p,n,k,a,b); prof[p]=bc
        print(f"  p={p:>8} (p/n^3={p/n**3:.2f}): w5..w12={[bc[w] for w in range(5,13)]}")
    for w in range(6,11):
        big=[prof[p][w] for p in primes if p>n**3]
        print(f"   band w={w} (d={1-w/n:.3f}) p>>n^3: {big} char-invariant={len(set(big))<=1}")
