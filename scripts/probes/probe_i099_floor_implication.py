# I099 closing: (a) confirm unstandardized kappa_4 is n-uniform (kappa_4*1 ~ const, kappa_4/sigma^4*n ~ const),
# (b) verify the sub-Gaussian tail-shape PREDICTS the floor: max_b|eta_b| ~ sqrt(2 n log(p/n)).
# Sub-Gaussian-leaning (kappa_4<0) => max <= matched-Gaussian max => exponent 1/2.
import numpy as np, sympy, math, sys
from math import comb
def cum(m,R):
    k=[0.0]*(R+1)
    for n in range(1,R+1):
        s=m[n]
        for j in range(1,n): s-=comb(n-1,j-1)*k[j]*m[n-j]
        k[n]=s
    return k
def periods(p,n,cap=4_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap)
    reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p; eta=np.empty(M,dtype=complex); CH=20000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]; eta[i:i+b.shape[0]]=np.exp(1j*w*((b*mu)%p)).sum(axis=1)
    return eta,M,mm
print("n-uniformity of kappa_4 + floor check. M=max|eta|, floor=sqrt(2 n log(p/n)) [matched-Gaussian max].")
print(f"{'p':>10} {'n':>4} {'m':>8} {'beta':>5} | {'k4(unstd)':>10} {'k4*n_std':>9} | {'M':>7} {'floor':>7} {'M/floor':>7} {'M/sqrtn':>8}")
for (p,n) in [(786433,16),(13631489,16),(13631489,32),(104857601,32),(104857601,64),(1811939329,64)]:
    if (p-1)%n or not sympy.isprime(p): 
        print(f"# skip {p} {n}"); sys.stdout.flush(); continue
    eta,M,mm=periods(p,n); re=eta.real-eta.real.mean()
    cm=[0.0]*5; cm[0]=1.0
    for r in range(1,5): cm[r]=np.mean(re**r)
    kap=cum(cm,4); sig=math.sqrt(kap[2]); k4u=kap[4]; k4s=kap[4]/sig**4*n
    Mx=np.abs(eta).max(); beta=math.log(p)/math.log(n)
    floor=math.sqrt(2*n*math.log(p/n))
    print(f"{p:>10} {n:>4} {mm:>8} {beta:>5.2f} | {k4u:>10.3f} {k4s:>9.3f} | {Mx:>7.2f} {floor:>7.2f} {Mx/floor:>7.4f} {Mx/math.sqrt(n):>8.3f}"); sys.stdout.flush()
