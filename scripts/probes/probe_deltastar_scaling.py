#!/usr/bin/env python3
"""
Scale the faithful delta* oracle: how does the worst-case epsMCA(delta) curve evolve
with n, and where does delta* sit (vs unique-decoding (1-rho)/2, Johnson 1-sqrt(rho))
as a function of the eps* band? Uses coset-reduced stacks; samples stacks when the
rep space is too big (>~4000 each) to stay tractable, else full-enum.
"""
import itertools, random
random.seed(7)
from probe_deltastar_groundtruth import consistent

def epsmca_curve(p,k,n,sample=None):
    pts=list(range(1,n+1))
    cws=[tuple(sum(co[j]*pow(x,j,p) for j in range(k))%p for x in pts)
         for co in itertools.product(range(p),repeat=k)]
    def reps():
        for tail in itertools.product(range(p),repeat=n-k):
            yield tuple([0]*k)+tail
    repl=list(reps()); nrep=len(repl)
    if sample and nrep*nrep>sample:
        pairs=[(random.choice(repl),random.choice(repl)) for _ in range(sample)]
    else:
        pairs=[(a,b) for a in repl for b in repl]
    best={t:0 for t in range(1,n+1)}
    for u0,u1 in pairs:
        if all(v==0 for v in u1): continue
        cnt={t:0 for t in range(1,n+1)}
        for g in range(p):
            line=tuple((u0[i]+g*u1[i])%p for i in range(n))
            hit={t:False for t in range(1,n+1)}
            for w in cws:
                A=[i for i in range(n) if w[i]==line[i]]
                if not A: continue
                if not (consistent(u0,A,pts,k,p) and consistent(u1,A,pts,k,p)):
                    for t in range(1,len(A)+1): hit[t]=True
            for t in range(1,n+1):
                if hit[t]: cnt[t]+=1
        for t in range(1,n+1):
            if cnt[t]>best[t]: best[t]=cnt[t]
    return best

print("RS instances: epsMCA(delta) worst-case curve; UD=(1-rho)/2, J=1-sqrt(rho)")
for (p,k,n,smp) in [(11,3,6,None),(11,4,8,4000),(13,4,8,4000),(13,5,10,4000),(11,5,10,4000)]:
    best=epsmca_curve(p,k,n,smp)
    rho=k/n; UD=(1-rho)/2; J=1-rho**0.5
    print(f"\nRS[F{p},k={k},n={n}] rho={rho:.2f} UD={UD:.3f} J={J:.3f}{' (sampled)' if smp else ''}")
    prev=None
    for t in range(n,0,-1):
        d=1-t/n; pr=best[t]/p
        mark=""
        if abs(d-UD)<0.5/n: mark+=" <-UD"
        if abs(d-J)<0.5/n: mark+=" <-Johnson"
        # flag the biggest jump
        if prev is not None and pr-prev>0.15: mark+=" *BIGJUMP*"
        print(f"   delta={d:.3f}  eps={pr:.3f}{mark}")
        prev=pr
