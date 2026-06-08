import itertools, math
import numpy as np
def probe(p, rho, eta, samples=3000, seed=1):
    rng=np.random.default_rng(seed); n=p; dom=np.arange(p)
    k=max(1,int(rho*n)); cap=1-k/n; johnson=1-(k/n)**0.5
    t=math.ceil((k/n+eta)*n); delta=1-t/n
    reg="below-Johnson" if delta<johnson else ("IN-BAND" if delta<cap else ">=cap")
    P=[]
    for coeffs in itertools.product(range(p),repeat=k):
        vec=np.zeros(n,dtype=np.int64)
        for cc in reversed(coeffs): vec=(vec*dom+cc)%p
        P.append(vec)
    P=np.array(P)
    R=rng.integers(0,p,size=(samples,n))
    ml=0
    for i in range(samples):
        cnt=int(((P==R[i]).sum(axis=1)>=t).sum())
        if cnt>ml: ml=cnt
    return n,k,round(cap,3),round(johnson,3),t,round(delta,3),reg,ml
for eta in [0.1,0.2]:
    print(f"FIXED gap eta={eta}, rate=0.5:")
    for p in [5,7,11]:
        n,k,cap,joh,t,d,reg,ml=probe(p,0.5,eta)
        print(f"  p={p:2d} k={k} cap={cap} john={joh} | agree>={t} radius={d} {reg} | MAXlist(sampled,3000)={ml}")
