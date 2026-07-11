import sys, math
sys.path.insert(0,'/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from probe_407_close_r1_ball import rou, build_ball, line_incidence, hv
import random
random.seed(4)
n,k=16,4; p=193; mu=rou(p,n); J=math.sqrt(n*k)
print(f"Characterize WHEN monomial is extremal vs beaten, by gap g=a*-b* and gcd(a*,b*,..).", flush=True)
print(f"n={n} k={k} J={J:.0f} p={p}. Deep band a=a*-1 (cofactor deg 1).\n", flush=True)
def test(astar,bstar):
    a=astar-1
    if a<=k: return None
    B=build_ball(mu,k,p,a,1)
    def far(u): return hv(u,k,n) not in B
    def bc(u0,u1): return line_incidence(hv(u0,k,n),hv(u1,k,n),p,B)
    if not(far({astar:1}) and far({bstar:1})): return ("mono-nonfar",)
    mono=bc({astar:1},{bstar:1})
    if mono==0: return ("mono=0",)
    best=mono;wit=None
    cand=[]
    for d in range(k,astar):
        for c in random.sample(range(1,p),min(p-1,30)): cand.append(({astar:1,d:c},{bstar:1}))
    for d in range(k,bstar):
        for c in random.sample(range(1,p),min(p-1,30)): cand.append(({astar:1},{bstar:1,d:c}))
    for _ in range(800):
        u0={astar:1};u1={bstar:1}
        for d in range(k,astar):
            if random.random()<.4: u0[d]=random.randrange(1,p)
        for d in range(k,bstar):
            if random.random()<.4: u1[d]=random.randrange(1,p)
        cand.append((u0,u1))
    for u0,u1 in cand:
        if not(far(u0) and far(u1)): continue
        v=bc(u0,u1)
        if v>best: best=v; wit=(u0,u1)
    return (mono,best,wit)
# test pairs with a=a*-1 > J (so a*>=10), various gaps
for astar in [10,11,12,13]:
  for bstar in range(astar-1, k-1, -1):
    g=astar-bstar
    from math import gcd
    r=test(astar,bstar)
    if r is None or r[0] in ("mono-nonfar","mono=0"):
      print(f"  (a*,b*)=({astar},{bstar}) gap={g}: {r[0]}"); continue
    mono,best,wit=r
    ratio=best/mono
    tag="EXTREMAL" if best==mono else f"BEATEN x{ratio:.2f}"
    print(f"  (a*,b*)=({astar},{bstar}) gap={g} gcd(a*,b*)={gcd(astar,bstar)}: mono={mono} max={best} {tag}", flush=True)
