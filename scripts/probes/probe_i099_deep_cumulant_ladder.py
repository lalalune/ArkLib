# I099 (STEP c1): standardized higher cumulants kappa_r/sigma^r of the period VALUE
# distribution {eta_b : b in quotient F_p*/mu_n}, mu_n = 2-power subgroup, n=2^mu, n|p-1, p>>n^3.
#   eta_b = sum_{x in mu_n} e_p(b x). Real linear functional Re(eta_b) is the object Slepian/Dudley
#   control for the matched-Gaussian comparison (OPEN LEMMA b). sup_b|eta_b| = sup over directions
#   of Re(omega eta_b), so sub-Gaussianity of the real marginal => the max ~ sqrt(2 log m)*sigma = the floor.
# DISTINCT from the DEAD even-moment/additive-energy route: this is the TAIL SHAPE of the value
# distribution (standardized cumulants), not E_r = sum|eta_b|^{2r}.
# TEST: as m=(p-1)/n grows (sample noise vanishes), do standardized cumulants settle to BOUNDED
# limits uniformly in n, or INFLATE at depth r~beta+1 (the forced anomaly = back to the wall)?
import numpy as np, sympy, math, sys
from math import comb
def cum(m,R):
    k=[0.0]*(R+1)
    for n in range(1,R+1):
        s=m[n]
        for j in range(1,n): s-=comb(n-1,j-1)*k[j]*m[n-j]
        k[n]=s
    return k
def periods_real(p,n,cap=4_000_000):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=np.array([pow(g,(mm*s)%(p-1),p) for s in range(n)],dtype=np.int64)
    M=min(mm,cap); sampled=mm>cap
    reps=np.array([pow(g,j,p) for j in range(M)],dtype=np.int64)
    w=2*np.pi/p
    eta=np.empty(M); CH=20000
    for i in range(0,M,CH):
        b=reps[i:i+CH][:,None]
        eta[i:i+b.shape[0]]=np.cos(w*((b*mu)%p)).sum(axis=1)
    return eta,mm,sampled
def iid_arcsine_std(n,R):
    mom=[0.0]*(R+1); mom[0]=1.0
    for k in range(2,R+1,2): mom[k]=comb(k,k//2)/2.0**k
    ks=cum(mom,R); sig=math.sqrt(n*ks[2])
    return {r:(n*ks[r])/sig**r for r in range(3,R+1)}
R=12
DEPTHS=[3,4,6,8,10,12]
print("I099 deep standardized cumulant ladder (Re eta_b over quotient). depth=12.")
print("Even k_r should -> bounded limit as m grows (sub-Gaussian-leaning); odd ~0 by symmetry.")
print(f"{'p':>11} {'n':>4} {'m':>9} {'beta':>5} {'samp':>5} | "+" ".join(f"k{r}".rjust(8) for r in DEPTHS))
cases=[(769,16),(12289,16),(786433,16),(50331649,16),
       (7681,32),(786433,32),(13631489,32),
       (40961,64),(13631489,64),(104857601,64)]
for (p,n) in cases:
    if (p-1)%n or not sympy.isprime(p):
        print(f"# skip {p} {n}"); sys.stdout.flush(); continue
    eta,m,samp=periods_real(p,n); eta=eta-eta.mean()
    cm=[0.0]*(R+1); cm[0]=1.0
    for r in range(1,R+1): cm[r]=np.mean(eta**r)
    kap=cum(cm,R); sig=math.sqrt(kap[2]); beta=math.log(p)/math.log(n)
    print(f"{p:>11} {n:>4} {m:>9} {beta:>5.2f} {str(samp):>5} | "+" ".join(f"{kap[r]/sig**r:>8.3f}" for r in DEPTHS)); sys.stdout.flush()
print("\ni.i.d.-arcsine sub-Gaussian reference limits (n-independent after standardizing):")
for n in [16,32,64]:
    ai=iid_arcsine_std(n,R)
    print(f" n={n:>3}: "+" ".join(f"k{r}={ai[r]:>7.3f}" for r in DEPTHS))
