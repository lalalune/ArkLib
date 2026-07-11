#!/usr/bin/env python3
"""THE DECISIVE ARITHMETIC: at what radius does the LADDER incidence cross the budget B=q*eps*~n?
The ladder at dyadic level s=2^mu, agreement parameter r (radius delta = 1 - r/s) realizes
incidence (the in-tree ceiling supply) = 2^r * C(2^{mu-1}, r)   [from kkh26_epsMCA_lower_bound: the
ladder gives eps_mca >= 2^r*C(s/2,r)/q, i.e. incidence = 2^r * C(s/2, r)].
BUT this is for a SINGLE dyadic level s. The OPTIMIZED ceiling picks the BEST s <= n.
At constant rate, the code degree k=(r-2)*m, n = s*m, so rho = (r-2)/s, i.e. r = rho*s + 2.

The ladder is BAD (incidence > B) when 2^r * C(s/2, r) > B. With r = rho*s+2:
  2^r * C(s/2, rho*s+2).  C(s/2, rho*s) -- but rho*s can EXCEED s/2 when rho>1/2! For rho<=1/2 ok.
  Hmm rho*s vs s/2: rho<=1/2 => rho*s <= s/2, valid binomial.
  log2[2^r C(s/2,r)] = r + log2 C(s/2, r) ~ r + (s/2) H_2(2 rho)   [since r/( s/2) = 2 rho]
Wait: r/(s/2) = (rho s)/(s/2) = 2 rho. So C(s/2, r) ~ 2^{(s/2) H_2(2 rho)}.
So log2(incidence) ~ rho*s + (s/2) H_2(2 rho) = s*(rho + H_2(2rho)/2).
Crosses B (log2 B) when s >= log2 B / (rho + H_2(2 rho)/2).
The DEEPEST radius (largest s, smallest 1-r/s? no: radius = 1 - r/s = 1 - rho - 2/s, deeper = larger s).
Largest usable s = n (m=1). So deepest ladder radius = 1 - rho - 2/n -- that's the DEEP BAND, ~ capacity!
NOT below the average term.

SO: the ladder's deepest radius (s=n) = 1 - rho - 2/n ~ capacity. The 'entropy ceiling'
1 - rho - H_2(rho)/log2 B comes from a DIFFERENT optimization. Let me recompute what radius the
ladder ACTUALLY certifies as bad, carefully, vs the claimed R2."""
from math import log2, comb, log
def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*log2(x)-(1-x)*log2(1-x)

print("Ladder bad-radius analysis. incidence(s,r) = 2^r * C(s/2, r), radius = 1 - r/s.")
print("At rate rho: the code is RS[k] with k=(r-2)*m, n=s*m -> rho=k/n=(r-2)/s, so r=rho*s+2.")
print("incidence > B  <=>  bad.  Find DEEPEST (smallest) radius that is still bad.\n")
print(f"{'rho':>5} {'nbits':>5} {'log2B':>6} | {'best_s':>7} {'r':>6} {'radius=1-r/s':>13} {'log2 incid':>11} {'avg-term R1':>11} {'ladder<avg?':>11}")
for rho in [0.5, 0.25, 0.125]:
    for nbits in [20,30,40]:
        n=2**nbits
        log2B = nbits        # B ~ n
        log2q = 128+nbits
        # average-term R1
        import math
        def h2nat(x):
            if x<=0 or x>=1: return 0.0
            return -x*math.log(x)-(1-x)*math.log(1-x)
        lnq=log2q*log(2); y=1-rho-(128.0/log2q)/n; x=y
        for _ in range(100): x=y-h2nat(x)/lnq
        R1=x
        # scan s (= dyadic level, s | n, s<=n), r = round(rho*s)+2, check bad, track deepest radius
        best=None
        s=4
        while s<=n:
            r=round(rho*s)+2
            if r<2 or r> s//2: 
                s*=2; continue
            # log2 incidence = r + log2 C(s/2, r)
            from math import lgamma
            def log2C(N,k_):
                if k_<0 or k_>N: return -1e18
                if k_==0 or k_==N: return 0.0
                return (lgamma(N+1)-lgamma(k_+1)-lgamma(N-k_+1))/log(2)
            log2incid = r + log2C(s//2, r)
            radius = 1 - r/s
            if log2incid > log2B:    # BAD
                # deepest = smallest radius among bad
                if best is None or radius < best[2]:
                    best=(s,r,radius,log2incid)
            s*=2
        if best:
            s,r,radius,li=best
            print(f"{rho:>5} {nbits:>5} {log2B:>6} | {s:>7} {r:>6} {radius:>13.6f} {li:>11.1f} {R1:>11.6f} {str(radius<R1):>11}")
        else:
            print(f"{rho:>5} {nbits:>5} {log2B:>6} | no bad ladder found")
