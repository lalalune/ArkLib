# Decisive: is the BINDING radius (deep, small I) DIRTY (q-dependent => wall) for rho=1/2?
# n=16 k=8 (rho=1/2): deep tau (small I_0) over many primes. r=tau-k; threshold (2k)^{2k/r}.
# If I varies over primes at the binding radius => delta* q-dependent => WALL confirmed.
import itertools
def isp(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True
def egcd(a,b):
    if b==0:return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,q):
    a%=q;g,x,_=egcd(a,q);return x%q
def subgroup(n,q):
    for c in range(2,q):
        h=pow(c,(q-1)//n,q)
        if pow(h,n,q)!=1:continue
        if n>1 and pow(h,n//2,q)==1:continue
        return [pow(h,i,q) for i in range(n)]
def matinv(M,q):
    t=len(M);A=[r[:]+[1 if i==j else 0 for j in range(t)] for i,r in enumerate(M)]
    for c in range(t):
        piv=next((r for r in range(c,t) if A[r][c]%q),None)
        if piv is None:return None
        A[c],A[piv]=A[piv],A[c];ip=inv(A[c][c],q);A[c]=[(x*ip)%q for x in A[c]]
        for r in range(t):
            if r!=c and A[r][c]%q:
                f=A[r][c];A[r]=[(A[r][j]-f*A[c][j])%q for j in range(2*t)]
    return [r[t:] for r in A]
def total_I(n,q,k,tau,elts):
    XS=[[pow(x,aa,q) for aa in range(n)] for x in elts]
    tot=0
    for a in range(k,n):
        for b in range(a+1,n):
            bad=set()
            for Sidx in itertools.combinations(range(n),tau):
                S=[elts[i] for i in Sidx]
                V=[[pow(x,j,q) for j in range(tau)] for x in S];Vi=matinv(V,q)
                if Vi is None:continue
                ok=True;al=None
                for r in range(tau-k):
                    pj=sum(Vi[k+r][i]*XS[Sidx[i]][a] for i in range(tau))%q
                    qj=sum(Vi[k+r][i]*XS[Sidx[i]][b] for i in range(tau))%q
                    if qj%q==0:
                        if pj%q:ok=False;break
                    else:
                        v=(-pj*inv(qj,q))%q
                        if al is None:al=v
                        elif al!=v:ok=False;break
                if ok and al is not None and al%q!=0:bad.add(al)
            tot+=len(bad)
    return tot
n=16;k=8  # rho=1/2
primes=[q for q in [97,193,257,353,449,577,641,769,929,1153,1409,2113,4129,8161] if isp(q) and (q-1)%n==0]
for tau in (10,11):
    r=tau-k; thr=(2*k)**(2*k//r) if r>0 else 0
    print(f"n=16 k=8 tau={tau} (delta={1-tau/n}, r=tau-k={r}, threshold (2k)^(2k/r)={thr}):",flush=True)
    vals=[]
    for q in primes:
        e=subgroup(n,q)
        if e is None:continue
        I=total_I(n,q,k,tau,e); vals.append(I)
        print(f"   q={q:5d}: I={I}",flush=True)
    print(f"   distinct I-values: {sorted(set(vals))}  -> {'DIRTY (q-dependent => WALL)' if len(set(vals))>1 else 'stable'}",flush=True)
