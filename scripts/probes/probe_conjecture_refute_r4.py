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
        # also try: seed f as agreeing with a few codewords (structured starts)
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
def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None:print(f"(p={p} n={n} no mu_n)",flush=True);return
    J=math.sqrt(n*k); reg = "n<=sqrt(p)" if n*n<=p else "n>sqrt(p)"
    print(f"\np={p} n={n} k={k} [{reg}: n={n} vs sqrt p={math.sqrt(p):.1f}] J={J:.2f}",flush=True)
    for a in range(k+1, math.ceil(J)+1):
        ml=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        ref = "  <<< REFUTES maxlist<=n-a !!!" if ml>(n-a) else ""
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} maxlist={ml:>2} n-a={n-a}{ref}",flush=True)
# HAMMER n<=sqrt(p), high restarts
run(p=73, n=8, k=2,rs=80,cl=50)
run(p=137,n=8, k=2,rs=60,cl=50)
run(p=101,n=10,k=2,rs=70,cl=55)
run(p=331,n=10,k=2,rs=50,cl=55)
run(p=109,n=9, k=3,rs=50,cl=40)
run(p=163,n=9, k=3,rs=40,cl=40)
run(p=197,n=14,k=2,rs=40,cl=60)   # sqrt(197)=14.03, n=14 boundary
