# Does Part B / room stay < 1 as r grows toward the saddle? n=8, sweep r=2,3,4,5,6. Honest: small n, exact.
import itertools
from collections import Counter
def find_subgroup(p,n):
    def ipr(g,p):
        x=1;s=set()
        for _ in range(p-1): x=x*g%p;s.add(x)
        return len(s)==p-1
    g=2
    while not ipr(g,p): g+=1
    h=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n): S.append(x);x=x*h%p
    return sorted(set(S))
def energies(S,p,r):
    sz=Counter()
    for t in itertools.product(S,repeat=r): sz[sum(t)]+=1
    Ez=sum(c*c for c in sz.values())
    sp=Counter()
    for s,c in sz.items(): sp[s%p]+=c
    Ep=sum(c*c for c in sp.values())
    return Ep,Ez
n=8
for p in [73,89]:
    S=find_subgroup(p,n)
    Ec={};W={}
    for r in range(1,8):
        Ep,Ez=energies(S,p,r);Ec[r]=Ez;W[r]=Ep-Ez
    print(f"--- n={n} p={p} ---")
    for r in range(2,7):
        N=n**(2*r)
        partB=p*(W[r+1]*Ec[r]-W[r]*Ec[r+1])
        room=N*n*(n-(2*r+1))*Ec[r]
        ok = room>=partB and room>0
        rat = partB/room if room!=0 else float('inf')
        print(f"  r={r}: room>0? {room>0}  PartB<=room? {ok}  ratio={rat:.4f}  (regime 2r+1<=n? {2*r+1<=n})")
