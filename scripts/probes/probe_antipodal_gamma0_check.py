import itertools
def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def find_prime(n,beta):
    t=((n**beta//n)+1)*n+1
    while not isprime(t): t+=n
    return t
def gen_sub(p,n):
    cof=(p-1)//n
    def order(a):
        o=1;x=a%p
        while x!=1: x=(x*a)%p;o+=1
        return o
    for c in range(2,p):
        h=pow(c,cof,p)
        if h!=1 and order(h)==n: return h
def inv(a,p): return pow(a,p-2,p)
for mu in (3,4,5):
    n=1<<mu; p=find_prime(n,4); g=gen_sub(p,n); MU=[pow(g,i,p) for i in range(n)]
    A,B=2,1
    pairs0=[]
    for i,j in itertools.combinations(range(n),2):
        x,y=MU[i],MU[j]
        num=(pow(y,A,p)-pow(x,A,p))%p; den=(pow(x,B,p)-pow(y,B,p))%p
        gamma=(num*inv(den,p))%p
        if gamma==0: pairs0.append((i,j))
    anti=[(i,(i+n//2)) for i in range(n//2)]
    neg_ok = all((p-MU[i])%p==MU[(i+n//2)%n] for i in range(n))
    match = set(pairs0)==set((i,j) for i,j in anti)
    print(f"n={n}: #pairs pinning g=0 = {len(pairs0)}; antipodal pairs = {len(anti)}; match={match}; neg_is_antipodal={neg_ok}")
