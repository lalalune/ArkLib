import sys; sys.path.insert(0,'/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from probe_407_close_r1_ball import rou, build_ball, line_incidence, hv
import itertools
n,k=16,4; astar,bstar,a,m=10,8,9,1
print(f"n={n} k={k} pencil(a*={astar},b*={bstar}) a={a}: does #bad grow with #free terms in f? (g=X^{bstar})")
for p in [193,257,353]:
    if (p-1)%n: continue
    mu=rou(p,n)
    B=build_ball(mu,k,p,a,m)
    def far(u): return hv(u,k,n) not in B
    def bc(u0): return line_incidence(hv(u0,k,n),hv({bstar:1},k,n),p,B)
    mono=bc({astar:1})
    # f = X^10 + (terms from {9,8,7,...} but not bstar=8 itself since that's g); free coeffs in F_p (sample best over a few)
    # 1 extra term (X^9): best over c
    best1=max((bc({astar:1,9:c}) for c in range(1,min(p,60))), default=0)
    # 2 extra terms (X^9,X^7): best over (c1,c2) sampled
    best2=0
    for c1 in range(0,min(p,12)):
        for c2 in range(0,min(p,12)):
            if c1==0 and c2==0: continue
            u={astar:1}
            if c1: u[9]=c1
            if c2: u[7]=c2
            if far(u): best2=max(best2,bc(u))
    print(f"  p={p}: mono={mono}  +1term(X^9)={best1}  +2term(X^9,X^7)={best2}  ratios: {best1/mono:.2f}, {best2/mono:.2f}", flush=True)
