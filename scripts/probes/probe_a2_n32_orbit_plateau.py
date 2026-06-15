# n=32 rho=1/8: full band profile for the worst direction(s), show the plateau and where I=16 starts.
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
def acore_leftover(R,n):
    Rs=set(R);h=n//2;paired=set()
    for j in R:
        if j in paired: continue
        if ((j+h)%n) in Rs: paired.add(j);paired.add((j+h)%n)
    return len([j for j in R if j not in paired])
def gm(mu,a,b,k,p,n):
    powr=[[pow(mu[i],j,p) for j in range(k)] for i in range(n)]
    za=[pow(mu[i],a,p) for i in range(n)];zb=[pow(mu[i],b,p) for i in range(n)]
    seen={}
    for A in itertools.combinations(range(n),k+1):
        M=[powr[i]+[(-zb[i])%p] for i in A];rhs=[za[i] for i in A]
        sol=solve(M,rhs,p)
        if sol is None: continue
        g=sol[k]
        if g==0 or g in seen: continue
        gg=sol[:k];R=[]
        for i in range(n):
            gi=0;xi=mu[i]
            for j in range(k-1,-1,-1): gi=(gi*xi+gg[j])%p
            if gi==(za[i]+g*zb[i])%p: R.append(i)
        seen[g]=tuple(R)
    return seen
n,k=32,4; p=find_prime(n,n**3*8); mu=rou(p,n); half=16
# inspect a few directions including the (16,17),(16,18),(8,9) etc
for (a,b) in [(16,17),(16,18),(16,24),(8,9),(4,5),(4,6),(5,7)]:
    g=gm(mu,a,b,k,p,n)
    prof=[]
    for w in range(k+1,n+1):
        cnt=sum(1 for R in g.values() if len(R)>=w)
        cc=sum(1 for R in g.values() if len(R)>=w and acore_leftover(R,n)<=1)
        if cnt>0: prof.append((w,cnt,cc))
    orbit=n//math.gcd(b-a,n)
    # first w where cnt<=budget=n
    firstle=next((w for (w,c,_) in prof if c<=n),None)
    print(f"dir({a},{b}) b-a={b-a} orbit=n/gcd={orbit}: firstW(I<=n)={firstle} (w-k={firstle-k if firstle else '-'}) "
          f"profile(w,I,Mann_core)={prof[:8]}")
