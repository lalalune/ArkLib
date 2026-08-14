# n=16: push r as deep as feasible. 16^(2r) state-space via incremental sumset. r up to 5 (dist over Z grows).
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
def energies_fast(S,p,rmax):
    Ec={};Wd={}; dist=Counter({0:1})
    for r in range(1,rmax+1):
        nd=Counter()
        for s,c in dist.items():
            for a in S: nd[s+a]+=c
        dist=nd
        Ez=sum(c*c for c in dist.values())
        sp=Counter()
        for s,c in dist.items(): sp[s%p]+=c
        Ep=sum(c*c for c in sp.values())
        Ec[r]=Ez;Wd[r]=Ep-Ez
    return Ec,Wd
n=16; p=257
S=find_subgroup(p,n)
Ec,Wd=energies_fast(S,p,6)
print(f"n={n} p={p}  saddle r~beta*log2(n)=4*4=16 (OUT of compute range; probing in-regime reach)")
print(f"regime 2r+1<=n holds for r<=7 (n-1)/2")
for r in range(2,6):
    N=n**(2*r)
    partB=p*(Wd[r+1]*Ec[r]-Wd[r]*Ec[r+1])
    room=N*n*(n-(2*r+1))*Ec[r]
    rat=partB/room if room>0 else float('inf')
    print(f"  r={r}: ratio={rat:.4f}  dom? {partB<=room and room>0}  room_coeff n-(2r+1)={n-(2*r+1)}  (in-regime? {2*r+1<=n})")
