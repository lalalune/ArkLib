import sys, math
sys.path.insert(0,'scripts/probes')
from prize_workspace import Workspace, isprime
import numpy as np

def faithful(n,beta):
    target=int(n**beta); m0=max(2,target//n)
    for m in range(m0,m0+400000):
        p=m*n+1
        if isprime(p) and p>n**3: return p
    return None
cases=[(16,faithful(16,4.0)),(32,faithful(32,4.0)),(64,faithful(64,4.0))]

print("=== E) LEE-YANG: partition fn Z(z)=prod_b (1 - z*eta_b^2) of the period 'spins'; do its zeros")
print("    pin to a circle (Lee-Yang) so that |max eta^2| is read off the zero closest to origin? ===")
for (n,p) in cases:
    W=Workspace(n,p); m2=np.unique(np.round(W.mag2[1:],6)); m2=m2[m2>1e-9]
    # zeros of Z(z) are z_b = 1/eta_b^2 -> smallest |z| = 1/max(eta^2). 'Lee-Yang' would need them on a curve.
    inv=1.0/m2; 
    # closest zero to origin pins the MAX. Real positive -> NOT on a circle (they're real). So Lee-Yang vacuous.
    print(f"  n={n:>3} p={p:>9}  1/max_eta2={inv.min():.3e}=zero_nearest -> recovers max={1/inv.min():.1f}; zeros real-positive (no LY circle)")

print("\n=== F) QUASICRYSTAL DIFFRACTION: mu_n as model set; Bragg peak heights = |eta_b|. Pure-point?")
print("    Test internal-space clustering: do the m period values concentrate (pure-point, peaks<=Cn) or spread? ===")
for (n,p) in cases:
    W=Workspace(n,p); m2=W.mag2[1:]
    # 'Bragg height <= C*n' would mean max|eta|^2 <= C^2 n. Check ratio max(eta^2)/n:
    Mmax=m2.max()
    print(f"  n={n:>3} p={p:>9}  max(eta^2)/n = {Mmax/n:>7.2f}  (Bragg<=Cn FALSE: grows as log(p/n)={math.log(p/n):.2f})")
