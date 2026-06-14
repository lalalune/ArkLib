import numpy as np, sympy
from math import comb
# Sub-Gaussian structural test: even-cumulant ladder of the period vs the i.i.d.-arcsine model.
# eta_b = sum_{x in mu_n} cos(2pi b x/q) (real). i.i.d. model: n independent cos(2pi U) ~ arcsine on [-1,1].
# If cumulants match i.i.d.-arcsine AND arcsine sub-Gaussian => period provably sub-Gaussian => closes upper.
def cumulants(samples, R):
    # central moments -> cumulants up to order 2R
    mu=samples.mean()
    c=samples-mu
    m=[np.mean(c**k) for k in range(2*R+1)]
    # cumulants via moment-cumulant (use numpy: kstat-like). do up to 8 by formula.
    k={}
    k[2]=m[2]
    k[4]=m[4]-3*m[2]**2
    k[6]=m[6]-15*m[4]*m[2]-10*m[3]**2+30*m[2]**3
    k[8]=m[8]-28*m[6]*m[2]-56*m[5]*m[3]-35*m[4]**2+420*m[4]*m[2]**2+560*m[3]**2*m[2]-630*m[2]**4
    return k
def realperiods(p,n):
    g=sympy.primitive_root(p); mm=(p-1)//n
    mu=[pow(g,(mm*s)%(p-1),p) for s in range(n)]
    return np.array([sum(np.cos(2*np.pi*(b*x%p)/p) for x in mu) for b in range(1,p)]), mm
# arcsine cos(2pi U) cumulants (per single term), times n for i.i.d. model
# single cos(2piU): even moments E[cos^{2r}]=C(2r,r)/4^r ; cumulants:
def arcsine_cumulants(n):
    M=[1,0]+[comb(2*r,r)/4**r if True else 0 for r in range(1,5)]  # m[0],m[1]=0,m[2]=1/2,...
    mm=[1.0,0.0]+[ (comb(2*r,r)/4.0**r) for r in range(1,5)]  # even moments at index 2,4,6,8
    # build full moment list index 0..8 (odd=0)
    mom=[0.0]*9; mom[0]=1
    for r in range(1,5): mom[2*r]=comb(2*r,r)/4.0**r
    k={}
    k[2]=mom[2]; k[4]=mom[4]-3*mom[2]**2
    k[6]=mom[6]-15*mom[4]*mom[2]+30*mom[2]**3
    k[8]=mom[8]-28*mom[6]*mom[2]-35*mom[4]**2+420*mom[4]*mom[2]**2-630*mom[2]**4
    return {r:n*k[r] for r in [2,4,6,8]}  # i.i.d. sum: cumulants add
print("even-cumulant ladder: period (measured) vs i.i.d.-arcsine model (n*single).  All <=0 for r>=2 => sub-Gaussian")
for (p,n) in [(769,16),(3329,16),(12289,16),(40961,16),(786433,16)]:
    if (p-1)%n: continue
    eta,m=realperiods(p,n); kp=cumulants(eta,4); ka=arcsine_cumulants(n)
    print(f"p={p} n={n} m={m}:")
    for r in [2,4,6,8]:
        print(f"    k{r}: period={kp[r]:>12.3f}   iid-arcsine={ka[r]:>10.3f}   sign={'<=0' if kp[r]<=1e-6 else '>0!'}")
