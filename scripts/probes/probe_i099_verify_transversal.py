# COUNTER-PROBE D: methodology audit. The probes use reps = g^j, j=0..m-1 as quotient reps for
# F_p*/mu_n. mu_n = <g^m>. Are these m=(p-1)/n values genuinely DISTINCT coset reps (one per class)?
# If g^j for j<m hit the same coset, the empirical distribution is wrong. Also: orbit-invariance
# eta_{zeta b}=eta_b means the VALUE is constant on cosets -- verify directly. And re-run k2,k4 with
# a SHUFFLED/alternative rep set (g^{j} for a random injection) to confirm no rep-ordering artifact.
import numpy as np, sympy, math
from math import comb
def cum(m,R):
    k=[0.0]*(R+1)
    for nn in range(1,R+1):
        s=m[nn]
        for j in range(1,nn): s-=comb(nn-1,j-1)*k[j]*m[nn-j]
        k[nn]=s
    return k
for (p,n) in [(786433,16),(13631489,32)]:
    g=sympy.primitive_root(p); m=(p-1)//n
    # reps g^j j=0..m-1: distinct cosets iff g^j mu_n distinct iff j distinct mod m. Yes by construction
    # (mu_n=<g^m>, so g^j mod mu_n <-> j mod m). VERIFY: collect canonical coset id = (discrete log) % m.
    reps=[pow(g,j,p) for j in range(m)]
    # canonical coset of element e: dlog(e) % m. We know reps[j]=g^j so coset = j%m = j (distinct). 
    # Direct orbit-invariance check: eta_b for b and zeta*b (zeta in mu_n) equal?
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    w=2*math.pi/p
    def eta(b): return sum(math.cos(w*((b*x)%p)) for x in mu)
    b=reps[7]; zeta=mu[3]; 
    e1=eta(b); e2=eta((zeta*b)%p)
    # full cumulants on reps vs on a DIFFERENT valid transversal: g^j * (random mu element) per j
    rng=np.random.default_rng(2)
    mun=np.array(mu,dtype=np.int64)
    reps2=[(pow(g,j,p)*mu[rng.integers(0,n)])%p for j in range(m)]
    def k24(reps):
        R=np.array(reps,dtype=np.int64)[:,None]
        val=np.cos(w*((R*mun)%p)).sum(axis=1); val=val-val.mean()
        cm=[0.0]*5; cm[0]=1.0
        for r in range(1,5): cm[r]=np.mean(val**r)
        kp=cum(cm,4); return kp[2],kp[4]
    k2a,k4a=k24(reps); k2b,k4b=k24(reps2)
    print(f"p={p} n={n} m={m}: orbit-inv |eta(b)-eta(zeta b)|={abs(e1-e2):.2e} (should be ~0)")
    print(f"   transversal A (g^j):       k2={k2a:.3f} (n={n}) k4={k4a:.3f} (-3n={-3*n})")
    print(f"   transversal B (g^j*rand mu):k2={k2b:.3f} (n={n}) k4={k4b:.3f} (-3n={-3*n})  [should MATCH A]")
