# COUNTER-PROBE B: push to n=128 (original probes maxed at n=64). The forced-anomaly danger
# is that the sub-Gaussian constant SECRETLY inflates as n grows / depth grows = back to BGK.
# Robust tests (NOT fragile high cumulants):
#   (1) variance = n exactly?  k4 = -3n exactly?  (extend the closed forms to n=128)
#   (2) MARGINAL sub-Gaussian: log-MGF of standardized Re-eta should stay <= t^2/2 (Gaussian) for
#       the FAVORABLE direction. Measure psi := max_t [log E e^{t Z} - t^2/2] over t in (0,3]; <=0 favorable.
#   (3) max_b|eta_b| vs floor sqrt(2 n log(p/n)); ratio should NOT creep up toward/over 1.
import numpy as np, sympy, math
from math import comb
def cum(m,R):
    k=[0.0]*(R+1)
    for nn in range(1,R+1):
        s=m[nn]
        for j in range(1,nn): s-=comb(nn-1,j-1)*k[j]*m[nn-j]
        k[nn]=s
    return k
def periods(p,n,cap=4_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap); reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p; eta=np.empty(M,dtype=complex); CH=10000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]; eta[i:i+b.shape[0]]=np.exp(1j*w*((b*mu)%p)).sum(axis=1)
    return eta,mm
print("COUNTER B: n up to 128. k2=n? k4=-3n? marginal psi2-excess (<=0 favorable)? M/floor creep?")
print(f"{'p':>12} {'n':>4} {'m':>9} {'beta':>5} | {'k2/n':>6} {'k4/(-3n)':>9} | {'psi_exc':>8} | {'M/floor':>8} {'M/sqrtn':>8}")
cases=[(786433,16),(13631489,32),(104857601,64),
       (33550337,128),(469762049,128),(2013265921,128)]
for (p,n) in cases:
    if (p-1)%n or not sympy.isprime(p):
        print(f"# skip {p} {n} (n|p-1={((p-1)%n==0)}, prime={sympy.isprime(p)})"); continue
    beta=math.log(p)/math.log(n)
    if beta < 3.0: print(f"# skip {p} {n} beta={beta:.2f}<3"); continue
    eta,mm=periods(p,n); re=eta.real-eta.real.mean()
    cm=[0.0]*5; cm[0]=1.0
    for r in range(1,5): cm[r]=np.mean(re**r)
    kap=cum(cm,4); k2=kap[2]; k4=kap[4]
    # standardized marginal psi2-excess
    z=re/math.sqrt(k2)
    psi=-1e9
    for t in np.linspace(0.25,3.0,24):
        lm=math.log(np.mean(np.exp(t*z)))-t*t/2
        psi=max(psi,lm)
    Mx=np.abs(eta).max(); floor=math.sqrt(2*n*math.log(p/n))
    print(f"{p:>12} {n:>4} {mm:>9} {beta:>5.2f} | {k2/n:>6.3f} {k4/(-3*n):>9.4f} | {psi:>8.4f} | {Mx/floor:>8.4f} {Mx/math.sqrt(n):>8.3f}")
