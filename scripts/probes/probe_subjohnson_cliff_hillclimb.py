# Hill-climb verification: can ANY word over mu_n (n<<p) beat L(4) = O(n)?
import random
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def find_prime(n, lo):
    p = lo - (lo%n) + 1
    while p<=lo or not is_prime(p): p+=n
    return p
def subgroup(n,p):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if g!=1 and pow(g,n,p)==1 and all(pow(g,n//d,p)!=1 for d in range(2,n+1) if n%d==0):
            D=[]; x=1
            for _ in range(n): D.append(x); x=x*g%p
            if len(set(D))==n: return D
    raise RuntimeError
def L4(w, D, p):
    n=len(D); pc=Counter()
    for i in range(n):
        for j in range(i+1,n):
            s=(w[j]-w[i])*pow(D[j]-D[i],p-2,p)%p
            b=(w[i]-s*D[i])%p
            pc[(s,b)]+=1
    cnt=0
    for c in pc.values():
        tt=2
        while tt*(tt-1)//2 < c: tt+=1
        if tt>=4: cnt+=1
    return cnt

n=24
p=find_prime(n,10_000_000)
D=subgroup(n,p)
rng=random.Random(1)
best=0; bestw=None
# 40 restarts x 250 steps, mutate one coordinate to a random field value, accept increases
for restart in range(40):
    # start: random word, or x^4-based
    if restart%3==0:
        w=[pow(x,4,p) for x in D]
    elif restart%3==1:
        w=[(pow(x,3,p)+rng.randrange(p)*pow(x,p-2,p))%p for x in D]
    else:
        w=[rng.randrange(p) for _ in range(n)]
    cur=L4(w,D,p)
    for step in range(250):
        i=rng.randrange(n); old=w[i]
        w[i]=rng.randrange(p)
        nv=L4(w,D,p)
        if nv>=cur: cur=nv
        else: w[i]=old
    if cur>best:
        best=cur; bestw=w[:]
print(f"n={n} p={p}: hill-climb max L(4) = {best}  (n/4 = {n//4}, n = {n}, 2n = {2*n})")
print(f"  best/n = {best/n:.2f}  -> {'LINEAR (cliff holds)' if best <= 3*n else 'SUPER-LINEAR (cliff broken!)'}")
