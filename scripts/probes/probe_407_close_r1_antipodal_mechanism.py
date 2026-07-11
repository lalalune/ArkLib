import sys, math
sys.path.insert(0,'/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from probe_407_close_r1_ball import rou, build_ball, line_incidence, hv
import itertools, random
random.seed(3)
n,k=16,4; p=193
mu=rou(p,n)
astar,bstar,a,mcof=10,8,9,1
B=build_ball(mu,k,p,a,mcof)
def far(u): return hv(u,k,n) not in B
def bc(u0,u1): return line_incidence(hv(u0,k,n),hv(u1,k,n),p,B)
print(f"p={p} (10,8) a=9. Pencil X^10+? = X^8*(X^2 + s*X + g). Vary cofactor structure.", flush=True)
# monomial: s=0 forced (no X^9 term). general: s free. Try all s for U0=X^10+s X^9.
print(f"  monomial s=0: bad={bc({10:1},{8:1})}")
counts={}
for s in range(0,p):
  u0={10:1} if s==0 else {10:1,9:s}
  if far(u0):
    counts[s]=bc(u0,{8:1})
vals=sorted(counts.values())
print(f"  over s in [0,{p}): far-count={len(counts)}  bad distribution: min={vals[0]} max={vals[-1]} median={vals[len(vals)//2]}")
print(f"  #s with bad=8: {sum(1 for v in counts.values() if v==8)},  bad=16: {sum(1 for v in counts.values() if v==16)},  bad>8: {sum(1 for v in counts.values() if v>8)}")
# Now: is the GENERAL extremal even more, via random multi-term U0 and U1 both?
best=max(counts.values()); bestwit=None
for _ in range(8000):
  u0={10:1};u1={8:1}
  for d in range(k,10):
    if random.random()<.5: u0[d]=random.randrange(1,p)
  for d in range(k,8):
    if random.random()<.5: u1[d]=random.randrange(1,p)
  if not(far(u0) and far(u1)): continue
  v=bc(u0,u1)
  if v>best: best=v; bestwit=(u0,u1)
print(f"  TRUE adversarial max over all far pencils (8000 trials): {best}  wit={bestwit}")
print(f"  => monomial bad=8 is {'NOT ' if best>8 else ''}extremal; general-cofactor (X^8*full-quadratic) reaches {max(counts.values())}")
