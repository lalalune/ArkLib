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
    # solve M x = b mod p, M is mxm. return x or None if singular/inconsistent
    m=len(M); A=[row[:]+[bvec[i]] for i,row in enumerate(M)]
    r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0: piv=i;break
        if piv is None: return None
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c],p-2,p)
        A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c]; A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]
def bandcounts(p,n,k,a,b):
    z=proot(p,n); pts=[pow(z,i,p) for i in range(n)]
    za=[pow(z,(i*a)%n,p) for i in range(n)]; zb=[pow(z,(i*b)%n,p) for i in range(n)]
    gammaagree={}
    for A in itertools.combinations(range(n),k+1):
        M=[]; rhs=[]
        for i in A:
            row=[pow(pts[i],j,p) for j in range(k)]+[(-za[i])%p]
            M.append(row); rhs.append(zb[i])
        sol=solve(M,rhs,p)
        if sol is None: continue
        g=sol[:k]; gamma=sol[k]
        # actual agreement of this gamma
        if gamma in gammaagree: continue
        cnt=0
        for i in range(n):
            gi=0; xi=pts[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(zb[i]+gamma*za[i])%p: cnt+=1
        gammaagree[gamma]=cnt
    return {w:sum(1 for v in gammaagree.values() if v>=w) for w in range(k+1,n+1)}
# n=16 k=4, the erratic pencils, primes from thin to p>>n^3=4096 (ideally ~n^4=65536)
n,k=16,4
primes=[p for p in [97,193,257,337,4129,8209,12289,65537,557057] if isp(p) and (p-1)%n==0]
for (a,b) in [(5,6),(5,7),(6,7),(9,11)]:
    g=math.gcd(b-a,n)
    print(f"pencil({a},{b}) gcd={g}:")
    prof={}
    for p in primes:
        bc=bandcounts(p,n,k,a,b); prof[p]=bc
        print(f"  p={p:>7} (p/n^3={p/n**3:.1f}): {[bc[w] for w in range(k+1,n+1)]}")
    # focus on binding window bands w=6,7 (above Johnson 1-sqrt(.25)=.5 -> w<8; capacity w=12)
    for w in [6,7]:
        vals=[prof[p][w] for p in primes]
        big=[prof[p][w] for p in primes if p>n**3]
        print(f"   band w={w} (delta={1-w/n:.3f}): all={vals} | p>>n^3 only={big} stable={len(set(big))<=1}")
