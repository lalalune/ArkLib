"""
probe_wfLA_scaling_law.py (lane wf-LA): WHICH scaling law does M obey at the prize slice?

From probe_wfLA_beta4_growth: at beta=4, C=M/sqrt(n log(p/n)) creeps as ~0.457+0.431 sqrt(log n).
That means M is NOT C0*sqrt(n log(p/n)) for a constant C0 -- there is an extra sqrt(log) creep.
Resolve the true law by comparing candidate fits across n=4..64 at fixed beta (exact FFT M):

  L1: M = C * sqrt(n * log(p/n))            [the prize-target near-Ramanujan-sqrt-log]
  L2: M = C * sqrt(n) * log(p/n)            [Johnson-ish, too big]
  L3: M = C * sqrt(n * log(p/n) * log n)    [sqrt(n) log n type]
  L4: M = C * sqrt(n) * sqrt(log p)         [the GaussianEnergyBound moment law sqrt(2e n ln q)]

Report the constant C for each law and its STABILITY (max/min across n). The law whose C is most
stable is the true scaling. This decides whether the in-tree NearRamanujanSqrtLog target (L1, C=O(1))
is actually ACHIEVED by the family, or whether the family needs L3/L4 (and L1 is unattainable).
"""
import math, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import Workspace, isprime

def prime_at_beta(n, beta):
    m0 = max(1, int(round(n**beta / n)))
    for d in range(0, 300000):
        for m in (m0+d, m0-d):
            if m<1: continue
            p = n*m+1
            if isprime(p): return m, p
    return None, None

laws = {
  "L1 sqrt(n log(p/n))":      lambda n,p: math.sqrt(n*math.log(p/n)),
  "L2 sqrt(n)*log(p/n)":      lambda n,p: math.sqrt(n)*math.log(p/n),
  "L3 sqrt(n log(p/n) log n)":lambda n,p: math.sqrt(n*math.log(p/n)*math.log(n)),
  "L4 sqrt(2e n ln p)":       lambda n,p: math.sqrt(2*math.e*n*math.log(p)),
}

for beta in (4.0, 4.5):
    print("="*78)
    print(f"beta = {beta}")
    print("="*78)
    data=[]
    for mu in range(2,7):
        n=1<<mu
        m,p = prime_at_beta(n,beta)
        if p is None or p>30_000_000: continue
        W=Workspace(n,p); M=W.M
        data.append((n,p,M))
    hdr = f"{'n':>5} {'M':>9} " + " ".join(f"{k.split()[0]:>6}" for k in laws)
    print(hdr)
    Cs = {k:[] for k in laws}
    for (n,p,M) in data:
        line=f"{n:>5} {M:>9.2f} "
        for k,f in laws.items():
            C = M/f(n,p); Cs[k].append(C)
            line += f"{C:>6.3f} "
        print(line)
    print("\n  constant stability (max/min ratio across n; ~1.00 => that law is the true scaling):")
    for k in laws:
        v=Cs[k]
        print(f"   {k:<26} C in [{min(v):.3f},{max(v):.3f}]  ratio={max(v)/min(v):.3f}")
    print()
