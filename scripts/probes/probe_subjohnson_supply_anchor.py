#!/usr/bin/env python3
"""Supply-side falsification anchor (#389 open core): sampled per-word explainable-core
counts at genuinely sub-Johnson instances ((k+m+1)^2 <= n(k-1)) sit at ~6x the random
mean C(n,t)/q^(m+1) (25-32 at the tuples below), two orders of magnitude below the
proven capped-fiber bound (4368-8008). Conjecture-shaped target for the wall:
B = polylog(n) * C(n,t)/q^(m+1). SAMPLED, not adversarial-exhaustive: structured
words were tested same-day: near-code = C(n-e,t) but cap-EXCLUDED; the quadratic-character word x^((q-1)/2) IS capped (agreement exactly 2k+m+1) with supply 258/215 vs mean 4/8 — the polylog target is FALSIFIED; corrected target: supply bounded by largest-agreement-class structure C(n/2,t)-shape (see issue comment)."""
import itertools, random, sys
from math import comb
if hasattr(sys.stdout,"reconfigure"): sys.stdout.reconfigure(encoding="utf-8")
random.seed(389)
def inv(a,p): return pow(a,p-2,p)
def fits(xs,ys,d,p):
    m=len(xs)
    if m<=d+1: return True
    base,bv=xs[:d+1],ys[:d+1]
    def ev(x):
        t=0
        for j in range(d+1):
            num=den=1
            for k2 in range(d+1):
                if k2!=j:
                    num=num*((x-base[k2])%p)%p; den=den*((base[j]-base[k2])%p)%p
            t=(t+bv[j]*num*inv(den%p,p))%p
        return t
    return all(ev(xs[i])==ys[i]%p for i in range(d+1,m))
for (q,n,k,m) in ((17,12,3,1),(31,16,3,1),(31,16,4,1)):
    t=k+m+1; dom=list(range(1,n+1)); best=0
    for _ in range(150):
        w=[random.randrange(q) for _ in range(n)]
        cnt=sum(1 for T in itertools.combinations(range(n),t)
                if fits([dom[i] for i in T],[w[i] for i in T],k-1,q))
        best=max(best,cnt)
    print(f"(q,n,k,m)=({q},{n},{k},{m}) subJ={t*t<=n*(k-1)}: sampled max={best}, "
          f"mean~{comb(n,t)//q**(m+1)}, proven-shape bound={comb(n,t)}")
