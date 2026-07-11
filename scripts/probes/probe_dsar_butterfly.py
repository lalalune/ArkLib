import numpy as np, math
def is_prime(n):
    if n<2: return False
    for d in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%d==0: return n==d
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in (1,n-1): continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: ok=True;break
        if not ok: return False
    return True
def find_prime(mu,bits):
    p=(1<<bits)
    while True:
        p+=1
        if (p-1)%mu==0 and is_prime(p): return p
def primitive_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac):return g
def analyze(p,n):
    g=primitive_root(p);gn=pow(g,(p-1)//n,p)
    mu=np.array([pow(gn,k,p) for k in range(n)],dtype=np.int64)
    g2=pow(gn,2,p);half=np.array([pow(g2,k,p) for k in range(n//2)],dtype=np.int64)
    rep=gn
    b=np.arange(1,p,dtype=np.int64)
    def etaset(S,bs):
        ph=np.exp(2j*np.pi*(np.outer(bs%p,S)%p)/p)
        return ph.sum(axis=1)
    CH=100000;Mn=0;Mh=0;best_b=0
    for i in range(0,len(b),CH):
        bb=b[i:i+CH]
        af=etaset(mu,bb);m=np.abs(af);j=int(np.argmax(m))
        if m[j]>Mn:Mn=m[j];best_b=int(bb[j])
        ah=etaset(half,bb);mh=float(np.abs(ah).max())
        if mh>Mh:Mh=mh
    a1=etaset(half,np.array([best_b]))[0];a2=etaset(half,np.array([(best_b*rep)%p]))[0]
    cos=(a1.real*a2.real+a1.imag*a2.imag)/(abs(a1)*abs(a2)+1e-30)
    return Mn,Mh,abs(a1),abs(a2),cos
for (bits,mu) in [(14,16),(14,32),(16,32),(16,64),(18,64)]:
    p=find_prime(mu,bits)
    Mn,Mh,a1,a2,cos=analyze(p,mu)
    print(f"p={p} n={mu}: M(n)={Mn:.3f} M(n/2)={Mh:.3f} ratio={Mn/Mh:.4f} (sqrt2={math.sqrt(2):.4f}) childmax/Mh={max(a1,a2)/Mh:.3f} cos@max={cos:+.3f}",flush=True)
