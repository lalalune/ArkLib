# Pin the CHAR-0 (q-free, p>>n^3) worst-case far-line incidence I(delta) at CONSTANT RATE,
# find where it crosses budget=n (=delta*), and compare to candidate closed forms.
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
def solve(M,bvec,p):
    m=len(M); A=[row[:]+[bvec[i]] for i,row in enumerate(M)]; r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0: piv=i;break
        if piv is None: return None
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],p-2,p); A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c]; A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]
def pencil_bands(p,n,k,a,b):
    z=proot(p,n); pts=[pow(z,i,p) for i in range(n)]
    za=[pow(z,(i*a)%n,p) for i in range(n)]; zb=[pow(z,(i*b)%n,p) for i in range(n)]
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
def deltastar(n,k,p):
    # worst-case over far pencils a,b in [k,n-1]\{n/2}: max I per band; find largest delta (smallest w) with worstI<=budget n
    best={w:0 for w in range(k+1,n+1)}
    fars=[x for x in range(k,n) if x!=n//2]
    for a in fars:
        for b in fars:
            if a<b:
                bc=pencil_bands(p,n,k,a,b)
                for w in bc: best[w]=max(best[w],bc[w])
    budget=n
    # delta*(largest delta) = smallest w with worstI(w)<=budget; report band profile
    cross=None
    for w in range(k+1,n+1):
        if best[w]<=budget: cross=w; break
    return best, cross
RES={}
for (n,k,p) in [(16,2,557057),(32,4,1179649),(16,4,557057)]:
    if not (isp(p) and (p-1)%n==0): 
        print(f"skip n={n} p={p}"); continue
    best,cross=deltastar(n,k,p)
    rho=k/n
    johnson=1-math.sqrt(rho); cap=1-rho
    dstar = 1-cross/n if cross else None
    print(f"n={n} k={k} rho={rho:.3f} p={p}: worstI per band {[best[w] for w in range(k+1,n+1)]}")
    print(f"   budget=n={n}; crossing band w={cross} -> delta*={dstar:.4f} | Johnson={johnson:.4f} cap={cap:.4f} | (cap-d*)={cap-dstar:.4f}  (cap-d*)*log2(n)={ (cap-dstar)*math.log2(n):.3f}")
    RES[(n,k)]=(dstar,rho,cap,johnson)
print("\n# Test closed-form: cap-delta* vs c/log2(n) and vs 1/n and H(rho)/(beta log n)")
for (n,k),(d,rho,cap,john) in RES.items():
    gap=cap-d
    print(f" n={n} rho={rho:.3f}: cap-d*={gap:.4f}  n*gap={n*gap:.2f}  gap*log2(n)={gap*math.log2(n):.3f}  gap*n/log2(n)={gap*n/math.log2(n):.3f}")
