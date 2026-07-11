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
    C=all_cws(D,k,p);n=len(D);best=0;bf=None
    for _ in range(rs):
        f=[rng.randrange(p) for _ in range(n)];cur=listsize(f,C,a)
        for _ in range(cl):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=listsize(f,C,a)
            if nl>=cur: cur=nl
            else: f[i]=old
        if cur>best:best=cur;bf=f[:]
    return best,bf
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
# PRODUCTION REGIME n <= sqrt(p): candidates that survived non-full-group
def cand(n,k,a):
    return {"2(n-a)+1":2*(n-a)+1, "k(n-a)+1":k*(n-a)+1, "2k-1":2*k-1, "n":n}
def run(p,n,k,rs,cl,sd=0):
    assert n*n<=p, f"n={n} not <= sqrt(p={p})"
    D=mun(p,n)
    if D is None:print(f"(p={p} n={n} no mu_n)",flush=True);return
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} [n<=sqrt(p): n={n} sqrt(p)={math.sqrt(p):.1f}] Johnson={J:.2f}",flush=True)
    for a in range(k+1, math.ceil(J)+1):
        ml,bf=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        cs=cand(n,k,a)
        v=" ".join(f"{nm}={b}{'!!REF' if ml>b else ''}" for nm,b in cs.items())
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} maxlist={ml:>2} (n-a={n-a}) | {v}",flush=True)
# n <= sqrt(p), aggressive
run(p=73, n=8, k=2,rs=40,cl=40)    # sqrt(73)=8.5, n=8
run(p=89, n=8, k=2,rs=40,cl=40)
run(p=101,n=10,k=2,rs=36,cl=44)    # sqrt(101)=10.05, n=10
run(p=151,n=10,k=2,rs=30,cl=44)
run(p=109,n=9, k=3,rs=30,cl=30)    # sqrt(109)=10.4, n=9, k=3
run(p=257,n=16,k=2,rs=24,cl=50)    # sqrt(257)=16.03, n=16 -> borderline n<=sqrt(p)
