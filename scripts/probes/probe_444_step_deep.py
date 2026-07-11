#!/usr/bin/env python3
"""
probe_444_step_deep.py (#444) -- moment-ratio STEP g(r) at DEEPER rungs (lead a). EXACT integer.

g(r) = (A_{r+1}/A_r)/((2r+1)*n),  A_r = E_r - n^{2r}/p  (DC-subtracted, MANDATORY at prize),
E_r = r-fold additive energy of mu_n = sum_t count(t)^2 over the distribution of sums of r subgroup
elements mod p, computed EXACTLY by integer sumset convolution (no size-p FFT). g(r)<1 <=> the Wick
STEP A_{r+1}/A_r <= (2r+1)n holds at rung r. Since A_{r+1}/A_r -> M^2 as r->inf, g(r*)<1 at r*~log p
approximates the BGK prize bound M <= sqrt((2r*+1)n) ~ sqrt(2n log p).

The board resolved ONLY r=2 (g(2)->1 as n->inf, "BGK knife-edge"). EXTENDING beyond r=2:

RESULT (exact; reproduces the board anchors g(2)=0.9363@n=32, g(3)=0.9063@n=32):
  At fixed n, g(r) DECREASES monotonically in r, obeying a clean law  1 - g(r,n) ~ r/n
  (n=32 increments .032 flat; n*slope = 1.00 +- 0.05). So at prize depth r*~4*log2(n) the margin
  r*/n -> 0 and g(r*) -> 1 FROM BELOW -- a BGK knife-edge at EVERY reachable rung, not just r=2.

  n=16: g(2..12) = .87 .81 .76 .70 .65 .61 .57 .53 .50 .47 .44  (r*~11)
  n=32: g(2..9)  = .936 .906 .878 .849 .819 .785 .748 .709      (r*~14)
  n=64: g(2..4)  = .968 .953 .941                                (r*~17)

RULE-3 (thin-essential? NO): a negation-closed RANDOM set of size n gives statistically identical
g(r) (thin within noise of neg-random). The sub-Wick deficit 1-g ~ r/n is the GENERIC leading
correction to pure Wick (A_r=(2r-1)!!n^r forces g==1), NOT a 2-power-subgroup signature.

VERDICT (REDUCE-TO-WALL, honest): telescoping g over r rebuilds the dead Wick/moment bound; g(r*)->1-
with NO power saving = the proven half-power gap as a genuine wall. The knife-edge is r-uniform (not
r=2-specific, correcting an earlier reading). g(r*)<1 at accessible n is the SAME M < sqrt(2n log p)
finite-n fact the sup-norm gate already has; the asymptotic decider is unreachable (r*~120 at n=2^30,
numerics can't decide < n=256, c.348). NOT prize-positive, NOT a refutation -- a precise direction map.
"""
import math
from collections import Counter
def is_prime(x):
    if x<2: return False
    if x%2==0: return x==2
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def find_prime(n,b):
    t=int(round(n**b)); p=t-(t%n)+1
    while p<=t or not is_prime(p): p+=n
    return p
def subgroup(n,p):
    for a in range(2,p):
        g=pow(a,(p-1)//n,p)
        if g!=1:
            x,o=g,1
            while x!=1 and o<=n: x=(x*g)%p; o+=1
            if o==n: return [pow(g,j,p) for j in range(n)]
def energies(n,p,rmax):
    base=subgroup(n,p); h=Counter({0:1}); E={0:1}
    for r in range(1,rmax+1):
        nh=Counter()
        for t,c in h.items():
            for x in base: nh[(t+x)%p]+=c
        h=nh; E[r]=sum(c*c for c in h.values())
    return E
if __name__=="__main__":
    print("g(r) deeper rungs, thin mu_n beta=4 (proper subgroup, large prime). 1-g ~ r/n law.")
    for n,rmax in [(16,13),(32,10),(64,5)]:
        p=find_prime(n,4.0); rstar=round(math.log(p)); E=energies(n,p,rmax)
        Ar=lambda r: E[r]-(n**(2*r))/p
        print(f"n={n} p={p} r*~{rstar}:")
        for r in range(2,rmax):
            g=(Ar(r+1)/Ar(r))/((2*r+1)*n)
            print(f"   r={r:>2}: g={g:.4f}  1-g={1-g:.4f}  (r/n={r/n:.4f})")
