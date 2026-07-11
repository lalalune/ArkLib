# I099 control: separate ARITHMETIC anomaly from finite-sample estimator NOISE.
# For each (p,n) compute period standardized cumulants k_r AND, as a null, the standardized
# cumulants of a TRUE i.i.d.-arcsine sample of the SAME size m (sum of n cos(2pi U), m draws).
# If period |k_r| <= iid-sample |k_r| band => deep cumulants are pure sampling noise, NO inflation.
# If period |k_r| >> iid band at depth r~beta+1 => the forced arithmetic anomaly (= wall). DECIDER.
import numpy as np, sympy, math, sys
from math import comb
rng=np.random.default_rng(0)
def cum(m,R):
    k=[0.0]*(R+1)
    for n in range(1,R+1):
        s=m[n]
        for j in range(1,n): s-=comb(n-1,j-1)*k[j]*m[n-j]
        k[n]=s
    return k
def stdcum(x,R):
    x=x-x.mean(); cm=[0.0]*(R+1); cm[0]=1.0
    for r in range(1,R+1): cm[r]=np.mean(x**r)
    kap=cum(cm,R); sig=math.sqrt(kap[2])
    return [kap[r]/sig**r for r in range(3,R+1)]
def periods_real(p,n,cap=4_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap)
    reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p; eta=np.empty(M); CH=20000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]; eta[i:i+b.shape[0]]=np.cos(w*((b*mu)%p)).sum(axis=1)
    return eta,M
R=12; DEPTHS=[4,6,8,10,12]
print("PERIOD vs i.i.d.-arcsine NULL (same m). [p]=period, band=mean+-2sd of 15 iid resamples.")
print("VERDICT per row: each depth r, is period inside null band (=> noise, no anomaly)?")
for (p,n) in [(786433,16),(13631489,32),(104857601,64)]:
    if (p-1)%n or not sympy.isprime(p): continue
    eta,m=periods_real(p,n); pk=stdcum(eta,R)
    # null: 15 iid-arcsine samples of size m
    null=[]
    for _ in range(15):
        U=rng.random((m,n)); s=np.cos(2*np.pi*U).sum(axis=1); null.append(stdcum(s,R))
    null=np.array(null)  # (15, len)
    idx={r:i for i,r in enumerate(range(3,R+1))}
    beta=math.log(p)/math.log(n)
    print(f"\np={p} n={n} m={m} beta={beta:.2f}:")
    for r in DEPTHS:
        i=idx[r]; mu_=null[:,i].mean(); sd=null[:,i].std()+1e-12; pv=pk[i]
        z=(pv-mu_)/sd
        inb = abs(z)<=2.5
        print(f"  k{r:>2}: period={pv:>9.3f}  null={mu_:>8.3f}+-{2*sd:>7.3f}  z={z:>6.2f}  {'NOISE(in band)' if inb else 'ANOMALY(out)'}")
    sys.stdout.flush()
