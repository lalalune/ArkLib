"""
probe_wfLA_random_baseline.py (lane wf-LA): is mu_n's M near the RANDOM-SET extreme value?

For a UNIFORM random n-subset of F_p, each |eta_b|^2 (b!=0) is ~ Exponential(mean n), and
M^2 = max over (p-1) iid ~ n*log(p) (Gumbel). So random predicts M ~ sqrt(n log p) and
M/sqrt(n log p) -> 1, M/sqrt(n log(p/n)) -> sqrt(log p / log(p/n)) = sqrt(beta/(beta-1)).

At beta=4 random predicts C_L1 = sqrt(4/3) = 1.155, and the EXTRA factor over a clean constant
comes from sqrt(log p) vs sqrt(log(p/n)). KEY TEST: does mu_n track the random Gumbel value, or
beat it (=> structured cancellation, the prize handle), or exceed it?

We compute, for each (n,p) at beta=4: mu_n's M, and the empirical mean+max of M over R random
n-subsets of F_p. If mu_n <= random-mean, mu_n is at-least-as-flat-as-random (good). The Gumbel
constant for L4=sqrt(2e n ln p) would be ~? -- we report mu_n's M / random-mean-M directly.
"""
import math, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import Workspace, isprime

def prime_at_beta(n, beta):
    m0 = max(1, int(round(n**beta / n)))
    for d in range(0, 300000):
        for m in (m0+d, m0-d):
            if m<1: continue
            p=n*m+1
            if isprime(p): return m,p
    return None,None

def random_M(n, p, R, rng):
    """max_{b!=0} |sum_{x in S} e_p(bx)| for R random n-subsets S; return (mean,max) over R."""
    Ms=[]
    for _ in range(R):
        S = rng.choice(p, size=n, replace=False)
        ind = np.zeros(p); ind[S]=1.0
        eta = np.fft.fft(ind)
        Ms.append(float(np.sqrt((np.abs(eta[1:])**2).max())))
    return float(np.mean(Ms)), float(np.max(Ms)), float(np.std(Ms))

rng = np.random.default_rng(0)
print("="*82)
print("beta=4: mu_n's M vs RANDOM n-subset M (Gumbel). ratio<1 => mu_n flatter than random.")
print("="*82)
print(f"{'n':>5} {'p':>12} {'M(mu_n)':>9} {'rand_mean':>10} {'rand_max':>9} {'mu/rmean':>9} {'gumbel_pred':>11}")
for mu in range(2,6):
    n=1<<mu
    m,p = prime_at_beta(n,4.0)
    if p is None or p>20_000_000: continue
    W=Workspace(n,p); Mmu=W.M
    R = 200 if p<2_000_000 else 40
    rm, rx, rs = random_M(n,p,R,rng)
    gumbel = math.sqrt(n*math.log(p))  # leading-order random prediction
    print(f"{n:>5} {p:>12} {Mmu:>9.2f} {rm:>10.2f} {rx:>9.2f} {Mmu/rm:>9.3f} {gumbel:>11.2f}")

print()
print("Interpretation: if mu_n/rand_mean ~ 1 across n => mu_n is RANDOM-LIKE (no structured")
print("cancellation handle; M tracks the Gumbel sqrt(n log p) = sqrt(beta/(beta-1)) * sqrt(n log(p/n))).")
print("That ratio sqrt(beta/(beta-1)) at beta=4 is %.3f -- compare to L1 constants observed."
      % math.sqrt(4/3))
print("If mu_n/rand_mean < 1 systematically => the deterministic family BEATS random = the prize lever.")
