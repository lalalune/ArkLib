import math
def mpow(a,e,p):
    r=1;a%=p
    while e>0:
        if e&1:r=r*a%p
        a=a*a%p;e>>=1
    return r
def isp(n):
    if n<2:return False
    d=2
    while d*d<=n:
        if n%d==0:return False
        d+=1
    return True
def find_p(n,lo):
    p=lo+((1+n-lo%n)%n)
    if p<=2:p+=n
    while True:
        if p>2 and p%n==1 and isp(p):return p
        p+=n
def proot(p):
    m=p-1;fs=[];d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fs.append(m)
    g=2
    while True:
        if all(mpow(g,(p-1)//f,p)!=1 for f in fs):return g
        g+=1
def dfo(r):
    v=1.0
    for j in range(1,r+1):v*=(2*j-1)
    return v
def run(n,beta):
    p=find_p(n,int(n**beta));g=proot(p);h=mpow(g,(p-1)//n,p)
    mu=[mpow(h,j,p) for j in range(n)];m=(p-1)//n;gn=mpow(g,n,p)
    eta=[];b=1
    for _ in range(m):
        re=sum(math.cos(2*math.pi*((b*x)%p)/p) for x in mu)
        eta.append(re);b=(b*gn)%p
    lnq=math.log(p);rstar=max(2,round(lnq/2))
    res=[sum(e**(2*r) for e in eta)/m/(dfo(r)*n**r) for r in range(1,rstar+4)]
    mx=max(res);amax=res.index(mx)+1
    print(f"n={n:3d} beta={beta} p={p} lnq={lnq:.1f} r*={rstar}  m_r*@band={res[rstar-1]:.3f}  MAX m_r={mx:.3f}@r={amax}  m1={res[0]:.4f}")
run(16,4.0);run(16,5.0);run(16,5.5)
run(32,4.0);run(32,5.0)
