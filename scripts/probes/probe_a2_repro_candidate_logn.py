# Reproduce the candidate doc's EXACT method for n=16,k=2 (rho=1/8) and n=16,k=4.
# Candidate's deltastar(): worst over far pencils a,b in [k,n)\{n/2}; budget=n;
# crossing = smallest w with worstI(w)<=budget. Then compare to my full-sweep (incl n/2).
import itertools, math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,lo):
    p=lo+(n-(lo%n))+1
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=n
def prim_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def rou(p,n):
    g=prim_root(p);w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]
def solve(M,bvec,p):
    m=len(M);A=[row[:]+[bvec[i]] for i,row in enumerate(M)];r=0
    for c in range(m):
        piv=None
        for i in range(r,m):
            if A[i][c]%p!=0:piv=i;break
        if piv is None:return None
        A[r],A[piv]=A[piv],A[r];inv=pow(A[r][c],p-2,p);A[r]=[(v*inv)%p for v in A[r]]
        for i in range(m):
            if i!=r and A[i][c]%p!=0:
                f=A[i][c];A[i]=[(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r+=1
    return [A[i][m]%p for i in range(m)]
# EXACT candidate pencil_bands: note candidate solves M=[powr|+(-za)], rhs=zb -> gamma multiplies x^a!
# i.e. candidate pencil is x^b + gamma x^a (gamma on the LOWER power a). Replicate EXACTLY.
def pencil_bands_candidate(p,n,k,a,b):
    z=rou(p,n);pts=z
    za=[pow(z[i],a,p) for i in range(n)];zb=[pow(z[i],b,p) for i in range(n)]
    powr=[[pow(pts[i],j,p) for j in range(k)] for i in range(n)]
    ga={}
    for A in itertools.combinations(range(n),k+1):
        M=[powr[i]+[(-za[i])%p] for i in A];rhs=[zb[i] for i in A]
        sol=solve(M,rhs,p)
        if sol is None: continue
        gamma=sol[k]
        if gamma in ga: continue
        g=sol[:k];cnt=0
        for i in range(n):
            gi=0;xi=pts[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+g[j])%p
            if gi==(zb[i]+gamma*za[i])%p: cnt+=1
        ga[gamma]=cnt
    return {w:sum(1 for v in ga.values() if v>=w) for w in range(k+1,n+1)}
def candidate_deltastar(n,k,p):
    best={w:0 for w in range(k+1,n+1)}
    fars=[x for x in range(k,n) if x!=n//2]
    for a in fars:
        for b in fars:
            if a<b:
                bc=pencil_bands_candidate(p,n,k,a,b)
                for w in bc: best[w]=max(best[w],bc[w])
    cross=None
    for w in range(k+1,n+1):
        if best[w]<=n: cross=w;break
    return best,cross
for (n,k,plo) in [(16,2,557057),(16,4,557057)]:
    if not (is_prime(plo) and (plo-1)%n==0):
        plo=find_prime(n,plo)
    best,cross=candidate_deltastar(n,k,plo)
    print(f"CANDIDATE method n={n} k={k} p={plo}: profile={[(w,best[w]) for w in range(k+1,n+1) if best[w]>0]}")
    print(f"   crossing w={cross} delta*={1-cross/n:.4f} w-k={cross-k} log2n={math.log2(n):.0f} gamma-on-LOWER-power-a, EXCLUDES n/2")
