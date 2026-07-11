import random
from itertools import product
def cw(co,D,p):
    o=[]
    for x in D:
        v=0;xp=1
        for c in co:v=(v+c*xp)%p;xp=(xp*x)%p
        o.append(v)
    return tuple(o)
def acw(D,k,p):return [cw(co,D,p) for co in product(range(p),repeat=k)]
def ls(f,C,a):return sum(1 for c in C if sum(1 for i in range(len(f)) if c[i]==f[i])>=a)
def mun(p,n):
    if (p-1)%n:return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None:return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None
def hammer(D,k,p,a,rs,cl,rng):
    C=acw(D,k,p);n=len(D);best=0
    for _ in range(rs):
        f=[rng.randrange(p) for _ in range(n)];cur=ls(f,C,a)
        for _ in range(cl):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=ls(f,C,a)
            if nl>=cur:cur=nl
            else:f[i]=old
        best=max(best,cur)
    return best
for (p,n,k,a) in [(73,8,2,3),(89,8,2,3),(137,8,2,3),(101,10,2,3)]:
    D=mun(p,n)
    mh=hammer(D,k,p,a,600,40,random.Random(7))
    flag = "<<MU EXCEEDS n-a!!!" if mh>(n-a) else "(capped <=n-a)"
    print("p=%d n=%d a=%d: mu_n ULTRA(600rs)=%d n-a=%d %s" % (p,n,a,mh,n-a,flag), flush=True)
print("R8DONE", flush=True)
