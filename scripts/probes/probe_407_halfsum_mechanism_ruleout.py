# REFINED MECHANISM: is e2(U) = sum of some k-subset of U^2 (the 2k squares), for every primitive U?
from itertools import combinations
def test(n,p,sizes,cap=400):
    HALF=n//2
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
    if g is None: return
    i2=pow(2,p-2,p); mun=[pow(g,j,p) for j in range(n)]
    nprim=0; ok=0; fail=[]
    for size in sizes:
        k=size//2
        for Uidx in combinations(range(n),size):
            if any(((j+HALF)%n) in set(Uidx) for j in Uidx): continue
            us=[mun[j] for j in Uidx]
            if sum(us)%p!=0 or sum(pow(u,3,p) for u in us)%p!=0: continue
            nprim+=1
            e2=(-i2*sum(pow(u,2,p) for u in us))%p
            Usq=[(u*u)%p for u in us]
            found=any(sum(W)%p==e2 for W in combinations(Usq,k))
            if found: ok+=1
            else: fail.append(tuple(Uidx))
            if nprim>=cap: break
        if nprim>=cap: break
    print(f"n={n} p={p}: primitive tested={nprim}; e2 = sum of k-subset of U^2 for {ok}/{nprim}"
          +(f"  FAIL e.g. {fail[0]}" if fail else "  ALL -> mechanism holds"))
for (n,p,sz) in [(16,17,[6]),(16,97,[6,8]),(32,97,[6]),(32,193,[6]),(32,257,[6]),(64,193,[6])]:
    test(n,p,sz)
