import sys, math
sys.path.insert(0,'/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from probe_407_close_r1_ball import rou, build_ball, line_incidence, hv
n,k=16,4
print(f"(10,8) a=9 beyond-Johnson({math.sqrt(n*k):.0f}); mono X^10+gX^8 vs X^10+cX^9+gX^8", flush=True)
for p in [97,193,257,353]:
  if (p-1)%n: continue
  mu=rou(p,n); astar,bstar,a,m=10,8,9,1
  B=build_ball(mu,k,p,a,m)
  def far(u): return hv(u,k,n) not in B
  def bc(u0,u1): return line_incidence(hv(u0,k,n),hv(u1,k,n),p,B)
  mono=bc({10:1},{8:1})
  best=0;bestc=None
  for c in range(1,p):
    u0={10:1,9:c}
    if far(u0):
      v=bc(u0,{8:1})
      if v>best: best=v;bestc=c
  print(f"  p={p}: mono={mono}  best(X^10+cX^9)={best}@c={bestc}  ratio={best/mono:.2f}", flush=True)
