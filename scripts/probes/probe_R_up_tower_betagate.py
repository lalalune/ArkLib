import cmath, math
from math import log, sqrt
def isprime(m):
    if m<2:return False
    if m%2==0:return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0:continue
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fac.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def v2(x):
    c=0
    while x%2==0:x//=2;c+=1
    return c
def Mof(p,n):
    g=primroot(p);h=pow(g,(p-1)//n,p)
    mun=[pow(h,j,p) for j in range(n)]
    w=2*math.pi/p
    return max(abs(sum(cmath.exp(1j*w*((b*y)%p)) for y in mun)) for b in range(1,p))
# identity check
p=12289;n=16
g=primroot(p);h=pow(g,(p-1)//n,p)
mun=[pow(h,j,p) for j in range(n)];muh=[pow(h,2*j,p) for j in range(n//2)]
w=2*math.pi/p
def eta(b,el):return sum(cmath.exp(1j*w*((b*y)%p)) for y in el)
maxerr=max(abs(eta(b,mun)-(eta(b,muh)+eta((b*h)%p,muh))) for b in range(1,200))
print(f"(A) exact identity max err = {maxerr:.2e}")
print(f"\n(B) R(n) up the tower at fixed prime (n=4,8,16,32,64). blow-up vs stable:")
print(f"{'p':>7} {'v2':>3} {'beta(n=64)':>10} " + " ".join(f"R({2**k})" for k in range(2,7)))
for p in [3329,7681,12289,40961,65537]:
    if not isprime(p):continue
    a=v2(p-1)
    rs=[]
    for k in range(2,7):
        nn=2**k
        if (p-1)%nn or (p-1)//nn<2: rs.append(None);continue
        if p>70000 and nn>32: rs.append(None);continue
        M=Mof(p,nn); rs.append(M/sqrt(nn*log((p-1)//nn)))
    bc=log(p)/log(64)
    print(f"{p:>7} {a:>3} {bc:>10.2f} " + " ".join((f"{r:5.3f}" if r else "  -- ") for r in rs))
