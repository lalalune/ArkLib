import sys, math
sys.path.insert(0, 'scripts/probes')
from prize_workspace import Workspace, isprime
import numpy as np

def faithful(n, beta):
    target=int(n**beta); m0=max(2,target//n)
    for m in range(m0, m0+400000):
        p=m*n+1
        if isprime(p) and p>n**3: return p
    return None

cases=[(16,faithful(16,4.0)),(32,faithful(32,4.0)),(64,faithful(64,4.0))]

print("=== C) LOG-GAS / COULOMB-GAS edge: treat real parts Re(eta_b) as a gas; is the spectral EDGE")
print("    (max) governed by a confining potential -> max ~ sqrt(2N) edge (RMT) or wall-driven? ===")
print("    Test: does max|eta| match a beta-ensemble edge a*sqrt(N) (N=#distinct periods=m), i.e. PHASE-BLIND RMT?")
for (n,p) in cases:
    W=Workspace(n,p); eta=W.eta[1:]
    re=eta.real; m=(p-1)//n  # number of distinct Gauss periods (each appears n times among b!=0)
    # distinct period values:
    # eta_b depends only on coset b*mu_n; there are m cosets -> m distinct |eta| (approx). 
    vals = np.abs(eta)
    # edge prediction from a Coulomb-gas at inverse temp from variance:
    var = (vals**2).mean()
    edge_rmt = math.sqrt(2*math.log(m))*math.sqrt(var)  # Gaussian max-of-m (white-noise) prediction
    edge_semicircle = 2*math.sqrt(var)*math.sqrt(m)/math.sqrt(m) # = 2 sqrt(var) (semicircle edge, scaled)
    print(f"  n={n:>3} p={p:>9} m={m:>7}  max|eta|={vals.max():>8.3f}  sqrt(var)={math.sqrt(var):>7.3f}  "
          f"WhiteNoiseMax=sqrt(2ln m)*sd={edge_rmt:>8.3f}  ratio(max/WNmax)={vals.max()/edge_rmt:>6.3f}")

print("\n=== D) SPECTRAL FORM FACTOR / level spacing of {eta_b^2}: log-correlated (FHK) vs white-noise? ===")
print("    Already MEASURED white-noise per meta-theorem. Confirm: nearest-neighbor spacing ratio <r> ~ 0.39 (Poisson) vs GUE 0.60 ===")
for (n,p) in cases:
    W=Workspace(n,p); m2=np.sort(W.mag2[1:])
    s=np.diff(m2); s=s[s>0]
    r=np.minimum(s[1:],s[:-1])/np.maximum(s[1:],s[:-1])
    print(f"  n={n:>3} p={p:>9}  <r>={r.mean():>6.3f}  (Poisson/white=0.386, GUE=0.603)")
