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
    return {
      "n-a+1":n-a+1,
      "k(n-a)+1":k*(n-a)+1,
      "(n-a+1)*ceil(log2n)":(n-a+1)*math.ceil(math.log2(n)),
      "ceil(k(n-a+1)/(a-k+1))":math.ceil(k*(n-a+1)/max(1,a-k+1)),
      "2(n-a)+1":2*(n-a)+1,
    }
def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None:print(f"(p={p} n={n} no mu_n)",flush=True);return
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} (p/n^2={p/n**2:.1f}) Johnson={J:.2f} cw={p**k}",flush=True)
    for a in range(k+1, math.ceil(J)+1):
        ml=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        cs=cand(n,k,a)
        v=" ".join(f"{nm}={b}{'!!REF' if ml>b else ''}" for nm,b in cs.items())
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} maxlist={ml:>3} | {v}",flush=True)
run(p=53,n=13,k=2,rs=16,cl=26)   # k=2 wider window, Johnson sqrt(26)=5.1
run(p=29,n=7, k=3,rs=18,cl=18)   # k=3 small, Johnson sqrt(21)=4.58, cw=24389
run(p=37,n=9, k=3,rs=14,cl=20)   # k=3, Johnson sqrt(27)=5.2, cw=50653
run(p=41,n=10,k=4,rs=12,cl=18)   # k=4, Johnson sqrt(40)=6.32, cw=41^4? too big -> skip if slow
