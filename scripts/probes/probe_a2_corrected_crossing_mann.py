# Corrected crossing = standard def: smallest w with worstI(w)<=budget=n AND worstI(w-1)>budget.
# Report I_0 vs Mann_core (antipodal pairs + <=1 leftover) at that band, and w_cross-k vs log2(n).
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
def acore(R,n):
    Rs=set(R);h=n//2;paired=set()
    for j in R:
        if j in paired: continue
        if ((j+h)%n) in Rs: paired.add(j);paired.add((j+h)%n)
    return len([j for j in R if j not in paired])  # leftover count
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
def run(n,k):
    p=find_prime(n,n**3*8);mu=rou(p,n);budget=n
    bI={w:0 for w in range(k+1,n+1)};bC=dict(bI)
    for a in range(k,n):
        for b in range(a+1,n):
            g=gm(mu,a,b,k,p,n)
            for w in range(k+1,n+1):
                cnt=sum(1 for R in g.values() if len(R)>=w)
                cc=sum(1 for R in g.values() if len(R)>=w and acore(R,n)<=1)
                if cnt>bI[w]: bI[w]=cnt;bC[w]=cc
    # standard crossing: smallest w with bI[w]<=budget and bI[w-1]>budget (or w=k+1)
    wc=None
    for w in range(k+1,n+1):
        prev=bI.get(w-1,10**9)
        if bI[w]<=budget and (w==k+1 or prev>budget): wc=w;break
    if wc is None:
        for w in range(k+1,n+1):
            if bI[w]<=budget: wc=w;break
    dstar=(n-wc)/n
    exact = (bI[wc]==bC[wc])
    return dict(n=n,k=k,rho=k/n,wc=wc,dstar=dstar,I0=bI[wc],core=bC[wc],exact=exact,
                wk=wc-k,log2n=math.log2(n))
gt={(8,2):0.375,(8,4):0.25,(16,4):0.5625,(16,8):0.3125}
print(" n  k  rho    wc  delta*   gt      I0  Mann_core  EXACT?  wc-k  log2n  wc-k==log2n?")
for (n,k) in [(8,2),(8,4),(16,2),(16,4),(16,8),(16,12)]:
    r=run(n,k)
    g=gt.get((n,k))
    gm_=(abs(r['dstar']-g)<1e-9) if g else "-"
    print(f"{r['n']:3d}{r['k']:3d} {r['rho']:5.3f} {r['wc']:3d}  {r['dstar']:.4f}  {str(g):>6}  {r['I0']:4d}  {r['core']:6d}    "
          f"{str(r['exact']):>5}   {r['wk']:3d}   {r['log2n']:.0f}    {r['wk']==round(r['log2n'])}")
