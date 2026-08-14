import sys, math
sys.path.insert(0, 'scripts/probes')
from prize_workspace import Workspace, isprime
import numpy as np

def faithful(n, beta):
    target = int(n**beta); m0 = max(2, target//n)
    for m in range(m0, m0+400000):
        p = m*n+1
        if isprime(p) and p > n**3: return p
    return None

# cap p ~ 2e7 for FFT feasibility -> n=16,32,64 at beta=4; smaller for higher beta
cases=[]
for n in [16,32,64]:
    p = faithful(n,4.0)
    if p and p < 30_000_000: cases.append((n,p))
# also a beta~4.5 small-n
for n in [16,32]:
    p = faithful(n,4.5)
    if p and p < 30_000_000: cases.append((n,p))

print("=== A) baseline M vs Johnson vs target ===")
print(f"{'n':>5} {'p':>10} {'M':>9} {'M/sqn':>7} {'C(M/sqrt(nlog(p/n)))':>22}")
WS={}
for (n,p) in cases:
    W=Workspace(n,p); WS[(n,p)]=W
    M=W.M; sqn=math.sqrt(n); rhs=math.sqrt(n*math.log(p/n))
    print(f"{n:>5} {p:>10} {M:>9.3f} {M/sqn:>7.3f} {M/rhs:>22.4f}")

print("\n=== B) HEAT TRACE thermodynamic functional Theta(t)=sum_b e^{-t eta_b^2}, eta_b^2=|eta_b|^2 ===")
print("    Does a t-derived bound on max eta_b^2 beat the 2nd-moment (mean) bound? log Theta - log of mean test.")
for (n,p) in cases:
    W=WS[(n,p)]; m2=W.mag2[1:]  # b!=0
    Mmax=m2.max()
    # spectral: max <= (1/t) log Theta_shifted; sharpest at large t. Compare to mean*p (2nd moment ceiling).
    mean=m2.mean()  # = (E_1 baseline) ~ n*(m)/(p) ... actually sum m2 = p*n - n^2
    # The heat-trace bound on max: for any t>0, max <= (1/t)*log(sum exp(t*m2)).  Find best (tightest) t numerically.
    best=1e18
    for t in np.logspace(-3, 1.5, 60)/Mmax:
        lse = math.log(np.exp(np.clip(t*m2 - t*Mmax,-700,0)).sum()) + t*Mmax
        bound = lse/t
        best=min(best,bound)
    # 2nd-moment-only ceiling: max <= sqrt(sum m2) trivially; but the *blind* bound is max<= sqrt(p*mean)
    blind = m2.sum()  # sum of all = p-1 moment; Johnson says max ~ mean-scale*log
    print(f"  n={n:>3} p={p:>9}  max eta^2={Mmax:>10.1f}  heat-best-bound={best:>10.1f}  ratio(heat/max)={best/Mmax:>6.3f}  mean*log(p)={mean*math.log(p):>10.1f}")
