# Round 6: binding test — random hill-climb (+ structured-poly seed) at larger n in n<=sqrt(p),
# deepest bands, hammering maxlist vs n-a.
import math, random
from itertools import product, combinations
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
def maxlist(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p);n=len(D);best=0
    for r in range(rs):
        # mix: some starts from a degree-a poly eval (structured), some random
        if r%3==0:
            co=[rng.randrange(p) for _ in range(a+1)]  # degree-a poly
            f=[ (lambda x:(lambda:sum(co[j]*pow(x,j,p) for j in range(a+1))%p)())(x) for x in D]
        else:
            f=[rng.randrange(p) for _ in range(n)]
        cur=listsize(f,C,a)
        for _ in range(cl):
            i=rng.randrange(n);old=f[i];f[i]=rng.randrange(p);nl=listsize(f,C,a)
            if nl>=cur: cur=nl
            else: f[i]=old
        best=max(best,cur)
    return best
def run(p,n,k,rs,cl,sd=0):
    assert n*n<=p
    D=mun(p,n)
    if D is None:print(f"(p={p} n={n} no mu_n)",flush=True);return
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} [n<=sqrt p: {n}<={math.sqrt(p):.1f}] J={J:.2f}",flush=True)
    for a in range(k+1, k+4):
        if a>=n: break
        ml=maxlist(D,k,p,a,rs,cl,random.Random(sd))
        ref="  <<<REFUTES maxlist<=n-a!!!" if ml>(n-a) else ""
        print(f"  a={a:>2} {'PAST' if a<J else ' - '} maxlist={ml:>2} n-a={n-a}{ref}",flush=True)
run(p=157,n=12,k=2,rs=60,cl=60)   # sqrt=12.5
run(p=211,n=14,k=2,rs=50,cl=70)   # sqrt=14.5
run(p=359,n=14,k=2,rs=40,cl=70)   # bigger field
print("===R6DONE===",flush=True)
