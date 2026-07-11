# COUNTER-PROBE A: Is kappa_4(Re eta_b) = -3n a genuine ARITHMETIC fact, or the trivial
# value an i.i.d. "random phases" model already produces? If trivial, it carries NO arithmetic
# information and the "sub-Gaussian-leaning" claim is just the CLT correction of a sum of n bounded vars.
#
# Model: Re eta_b = sum_{x in mu_n} cos(2pi b x /p). For "generic" b the n phases {b x mod p}
# look like n independent uniform points. For Y=cos(2pi U), U~Unif: E Y=0, EY^2=1/2, EY^4=3/8.
# kappa_2(Y)=1/2, kappa_4(Y)=EY^4-3(EY^2)^2 = 3/8 - 3/4 = -3/8. For a sum of n iid: kappa_4 = n*(-3/8).
# That is NOT -3n. So if the period gives EXACTLY -3n (=8x bigger), that's a real arithmetic structure
# (the phases are NOT independent: subgroup sum-freeness / the x_i are roots of unity, correlated).
import numpy as np, sympy, math
from math import comb
def cum(m,R):
    k=[0.0]*(R+1)
    for nn in range(1,R+1):
        s=m[nn]
        for j in range(1,nn): s-=comb(nn-1,j-1)*k[j]*m[nn-j]
        k[nn]=s
    return k
def re_periods(p,n,cap=4_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap); reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p; eta=np.empty(M); CH=20000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]; eta[i:i+b.shape[0]]=np.cos(w*((b*mu)%p)).sum(axis=1)
    return eta
print("COUNTER A: period kappa_4 vs iid-phase model kappa_4 (=-3n/8) and full-iid-arcsine.")
print("If period = -3n EXACTLY and iid-phase = -3n/8, the period 4th-cumulant IS arithmetic (8x).")
print(f"{'p':>10} {'n':>4} {'m':>8} | {'k4_period':>10} {'iid_phase=-3n/8':>16} {'ratio':>7} | {'k2_period':>9} {'iid k2=n/2':>10}")
for (p,n) in [(786433,16),(13631489,32),(104857601,64),(13631489,16),(104857601,32)]:
    if (p-1)%n or not sympy.isprime(p): continue
    eta=re_periods(p,n); eta=eta-eta.mean()
    cm=[0.0]*5; cm[0]=1.0
    for r in range(1,5): cm[r]=np.mean(eta**r)
    kap=cum(cm,4); k2=kap[2]; k4=kap[4]
    print(f"{p:>10} {n:>4} {len(eta):>8} | {k4:>10.3f} {-3*n/8:>16.3f} {k4/(-3*n/8):>7.3f} | {k2:>9.3f} {n/2:>10.3f}")
