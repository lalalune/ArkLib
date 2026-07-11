# Crossing under BOTH conventions: (A) include n/2  (B) exclude n/2.  Mann_core exactness + w-k vs log2n.
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
def crossing(bI,bC,n,k,budget):
    wc=None
    for w in range(k+1,n+1):
        prev=bI.get(w-1,10**9)
        if bI[w]<=budget and (w==k+1 or prev>budget): wc=w;break
    if wc is None:
        for w in range(k+1,n+1):
            if bI[w]<=budget: wc=w;break
    return wc
def run(n,k):
    p=find_prime(n,n**3*8);mu=rou(p,n);budget=n;half=n//2
    # band profiles for both conventions in one pass
    bI_all={w:0 for w in range(k+1,n+1)};bC_all=dict(bI_all)
    bI_nh =dict(bI_all);bC_nh =dict(bI_all)
    for a in range(k,n):
        for b in range(a+1,n):
            g=gm(mu,a,b,k,p,n)
            isnh = (a!=half and b!=half)
            for w in range(k+1,n+1):
                cnt=sum(1 for R in g.values() if len(R)>=w)
                cc=sum(1 for R in g.values() if len(R)>=w and acore_leftover(R,n)<=1)
                if cnt>bI_all[w]: bI_all[w]=cnt;bC_all[w]=cc
                if isnh and cnt>bI_nh[w]: bI_nh[w]=cnt;bC_nh[w]=cc
    wcA=crossing(bI_all,bC_all,n,k,budget)
    wcB=crossing(bI_nh ,bC_nh ,n,k,budget)
    return dict(n=n,k=k,rho=k/n,log2n=math.log2(n),
                A=(wcA,bI_all[wcA],bC_all[wcA],wcA-k),
                B=(wcB,bI_nh[wcB],bC_nh[wcB],wcB-k))
print("conv A=incl n/2, conv B=excl n/2.  (wc, I0, Mann_core, wc-k)")
print(" n  k  rho   log2n |  A:incl-n/2 (wc,I0,core,wc-k)  exact?  |  B:excl-n/2 (wc,I0,core,wc-k)  exact? B_wc-k==log2n?")
for (n,k) in [(8,2),(8,4),(16,2),(16,4),(16,8)]:
    r=run(n,k)
    wA,iA,cA,kA=r['A'];wB,iB,cB,kB=r['B']
    print(f"{n:3d}{k:3d} {r['rho']:5.3f}  {r['log2n']:.0f}    | ({wA},{iA},{cA},{kA})  {iA==cA}   "
          f"| ({wB},{iB},{cB},{kB})  {iB==cB}   B_logn={kB==round(r['log2n'])}")
