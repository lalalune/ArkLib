#!/usr/bin/env python3
"""Pin where realized-max log2|N| crosses p~2^128 (the fixed prize budget). m=n/2.
Worst pattern is weight ~m (all-ones reduced). Confirm + measure max for n=64,96,112,128.
This locates the EXACT n where the norm gate transitions from closeable to dead."""
import numpy as np, math, random, time
def maxN(n, tbudget=35):
    m=n//2
    k=np.arange(m); W=np.exp(1j*np.pi*(2*k+1)/m)
    V=np.vander(W, m, increasing=True)
    def l2(c):
        av=np.abs(V@np.asarray(c,dtype=float))
        if np.any(av<1e-9): return None
        return float(np.sum(np.log2(av)))
    random.seed(3)
    best=-1; bestc=None; t0=time.time()
    # bias toward high weight where the max lives
    while time.time()-t0<tbudget:
        w=random.randint(int(0.7*m), m)
        c=[0]*m
        for i in random.sample(range(m),w): c[i]=random.choice([-1,1])
        v=l2(c)
        if v is not None and v>best: best=v; bestc=c[:]
    # quick hill climb
    t1=time.time()
    imp=True
    while time.time()-t1<25 and imp:
        imp=False
        for j in random.sample(range(m),m):
            for nv in (-1,0,1):
                if bestc[j]==nv: continue
                cand=bestc[:]; cand[j]=nv
                if not any(cand): continue
                v=l2(cand)
                if v is not None and v>best: best=v; bestc=cand; imp=True
    return best, sum(1 for x in bestc if x)

for n in [64,96,112,128]:
    b,w=maxN(n)
    print(f"n={n:>3}: max log2|N| (lb) = {b:7.2f} at weight {w}  | p~2^128 => gate {'DEAD' if b>128 else 'closeable'}", flush=True)
