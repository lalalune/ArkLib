import itertools, math
from collections import Counter
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=1
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
def worst_list(p,H,w,k,a_min):
    n=len(H); found=set()
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]; ys=[w[i] for i in sub]
        if len(set(xs))!=k:continue
        ev=tuple(interp_eval(p,xs,ys,H[j]) for j in range(n))
        if sum(1 for j in range(n) if ev[j]==w[j])>=a_min: found.add(ev)
    return found
def analyze(n,k):
    p=find_prime(n,2*n)
    if p>120:return
    (H,g)=subgroup(p,n); rho=k/n; d=k+1   # word x^{k+1}
    w=[pow(x,d,p) for x in H]
    aJ=math.sqrt((k-1)*n)
    scale=pow(g,(p-1-d)% (p-1),p)  # g^{-d} mod p
    def sigma(ev): return tuple(scale*ev[(j+1)%n]%p for j in range(n))
    print(f"\nn={n} k={k} p={p} rho={rho:.3f} word=x^{d}  Johnson a*={aJ:.2f}")
    for a in range(k+1,n):
        L=worst_list(p,H,w,k,a)
        if len(L)<2:
            if a>k+2:break
            continue
        closed=all(sigma(ev) in L for ev in L)
        seen=set();orbits=[]
        for ev in L:
            if ev in seen:continue
            orb=0;cur=ev
            while cur not in seen:
                seen.add(cur);orb+=1;cur=sigma(cur)
            orbits.append(orb)
        side="below-J" if a>aJ else "BEYOND-J"
        print(f"  a={a} d={1-a/n:.3f} [{side}] list={len(L):3d} sigma-closed={closed} #orbits={len(orbits)} orbit-sizes={dict(Counter(orbits))}")
for (n,k) in [(8,4),(16,4),(16,8),(16,12)]:
    analyze(n,k)
