import itertools, math
from collections import Counter
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def primes_for(n,count,lo):
    out=[];p=lo
    while len(out)<count:
        if (p-1)%n==0 and is_prime(p):out.append(p)
        p+=1
    return out
def subgroup(p,n):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if len({pow(g,i,p) for i in range(n)})==n:return [pow(g,i,p) for i in range(n)],g
def interp_eval(p,xs,ys,X):
    fx=0
    for i in range(len(xs)):
        num=ys[i]%p; den=1
        for l in range(len(xs)):
            if l==i:continue
            num=num*((X-xs[l])%p)%p; den=den*((xs[i]-xs[l])%p)%p
        fx=(fx+num*pow(den,p-2,p))%p
    return fx
def orbit_count(p,n,k,d,a_min):
    (H,g)=subgroup(p,n)
    w=[pow(x,d,p) for x in H]
    scale=pow(g,(p-1-d)%(p-1),p)
    def sigma(ev):return tuple(scale*ev[(j+1)%n]%p for j in range(n))
    L=set()
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]
        if len(set(xs))!=k:continue
        ys=[w[i] for i in sub]
        ev=tuple(interp_eval(p,xs,ys,H[j]) for j in range(n))
        if sum(1 for j in range(n) if ev[j]==w[j])>=a_min: L.add(ev)
    seen=set();norb=0;sizes=[]
    for ev in L:
        if ev in seen:continue
        norb+=1;cur=ev;s=0
        while cur not in seen:
            seen.add(cur);cur=sigma(cur);s+=1
        sizes.append(s)
    return len(L),norb,dict(Counter(sizes))
# Test p-independence: same (n,k,d,a) across several primes
print("== p-independence of #orbits ==")
for (n,k,d,a) in [(16,4,5,5),(16,8,9,9),(16,8,9,10),(8,4,5,5)]:
    row=[]
    for p in primes_for(n,4,2*n):
        if p>400:break
        L,no,sz=orbit_count(p,n,k,d,a)
        row.append((p,L,no))
    print(f" n={n} k={k} word=x^{d} a={a} (δ={1-a/n:.3f}): "+"  ".join(f"p={p}:list={L},orb={no}" for p,L,no in row))
