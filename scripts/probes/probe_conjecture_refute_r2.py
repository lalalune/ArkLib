import math, random
from itertools import product
def codeword(co,D,p):
    out=[]
    for x in D:
        v=0;xp=1
        for c in co: v=(v+c*xp)%p; xp=(xp*x)%p
        out.append(v)
    return tuple(out)
def all_cws(D,k,p): return [codeword(co,D,p) for co in product(range(p),repeat=k)]
def listsize(f,C,a):
    cnt=0
    for c in C:
        ag=0
        for i in range(len(f)):
            if c[i]==f[i]: ag+=1
        if ag>=a: cnt+=1
    return cnt
def maxlist(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p);n=len(D);best=0
    for _ in range(rs):
        f=[rng.randrange(p) for _ in range(n)];cur=listsize(f,C,a)
        for _ in range(cl):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=listsize(f,C,a)
            if nl>=cur: cur=nl
            else: f[i]=old
        best=max(best,cur)
    return best
def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None:return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None
def cand(n,k,a):
    return {"n":n, "(n-a)+k+1":(n-a)+k+1, "2(n-a)+1":2*(n-a)+1, "k(n-a)+1":k*(n-a)+1}
def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None:print(f"(p={p} n={n} no mu_n)",flush=True);return
    J=math.sqrt(n*k)
    reg="SMALL" if p<n*n else "LARGE"
    print(f"\np={p} n={n} k={k} [{reg} p/n^2={p/n**2:.1f}] Johnson={J:.2f}",flush=True)
    for a in range(k+1, math.ceil(J)+2):
        ml=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        cs=cand(n,k,a)
        v=" ".join(f"{nm}={b}{'!!REF' if ml>b else ''}" for nm,b in cs.items())
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} maxlist={ml:>3} (n-a={n-a}) | {v}",flush=True)
# k=2, both regimes, several n; aggressive search at deepest band a=k+1
run(p=17, n=16,k=2,rs=24,cl=40)   # SMALL, deep window
run(p=97, n=16,k=2,rs=20,cl=40)   # LARGE
run(p=31, n=15,k=2,rs=24,cl=36)   # SMALL
run(p=23, n=11,k=2,rs=30,cl=30)   # SMALL deep
run(p=13, n=12,k=2,rs=30,cl=30)   # SMALL very deep (p~n)
