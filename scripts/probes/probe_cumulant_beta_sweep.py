import math
def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,target):
    p=target-(target%n)+1
    for d in range(0,8*n,n):
        if is_prime(p+d):return p+d
        if p-d>n and is_prime(p-d):return p-d
    return None
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return [pow(g,i,p) for i in range(n)]
def dfact(m):
    r=1;k=m
    while k>0:r*=k;k-=2
    return r
def analyze(n,p,rmax):
    H=subgroup(p,n);tp=2*math.pi;etas=[]
    for b in range(1,p):
        c=0.0
        for x in H:c+=math.cos(tp*((b*x)%p)/p)
        etas.append(c)
    maxratio=0;worstr=0
    for r in range(1,rmax+1):
        Cr=sum(e**(2*r) for e in etas)
        ratio=Cr/(p*dfact(2*r-1)*(n**r))
        if ratio>maxratio:maxratio=ratio;worstr=r
    M=max(abs(e) for e in etas)
    return maxratio,worstr,M
print("β-sweep at n=16: heavy→healthy transition vs n/√p (heavy window ≈0.25-0.5 = β≈2)")
print(f"{'β':>5} {'p':>9} {'n/√p':>7} {'maxρ_r':>8} {'@r':>3} {'M/√n':>6} {'M/floor':>8} {'verdict':>9}")
n=16
for beta in [2.0,2.3,2.6,3.0,3.5,4.0,4.5,5.0]:
    target=int(round(n**beta))
    if target>2_500_000: continue
    p=find_prime(n,target)
    if not p: continue
    rmax=min(12,int(math.log(p))+2)
    mr,wr,M=analyze(n,p,rmax)
    nsp=n/math.sqrt(p); floor=math.sqrt(2*n*math.log(p))
    v="HEAVY" if mr>1.1 else "healthy"
    print(f"{math.log(p)/math.log(n):>5.2f} {p:>9} {nsp:>7.3f} {mr:>8.2f} {wr:>3} {M/math.sqrt(n):>6.2f} {M/floor:>8.2f} {v:>9}",flush=True)
