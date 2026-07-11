import sys; sys.path.insert(0,'/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from probe_407_close_r1_ball import rou, build_ball, line_incidence, hv
from math import gcd
n,k=16,4
print(f"n={n} k={k}: does the monomial->general overcount FACTOR scale with cofactor period m=gcd(a-b,n)?")
# pencils with varying m: (a,b) with a-b giving m=2,4,8
configs=[(10,8,'m=gcd(2,16)=2'),(12,8,'m=gcd(4,16)=4'),(12,4,'m=gcd(8,16)=8')]
for (astar,bstar,lbl) in configs:
    mm=gcd(astar-bstar,n)
    for p in [257,353]:
        if (p-1)%n: continue
        mu=rou(p,n)
        # agreement a: beyond Johnson sqrt(nk)=8; use a=9
        a=9
        B=build_ball(mu,k,p,a,1)
        def far(u): return hv(u,k,n) not in B
        def bc(u): return line_incidence(hv(u,k,n),hv({bstar:1},k,n),p,B)
        mono=bc({astar:1})
        # best combo: add a free middle term
        best=0
        for e in range(bstar+1,astar):
            for c in range(1,min(p,40)):
                u={astar:1,e:c}
                if far(u): best=max(best,bc(u))
        print(f"  ({astar},{bstar}) {lbl} (m={mm}): p={p} mono={mono} combo_best={best} factor={best/max(mono,1):.2f}", flush=True)
        break
