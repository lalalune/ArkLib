import sympy as sp
from math import comb, factorial
m=sp.symbols('m'); n=sp.symbols('n')
def Bvals(K,R):
    Ks=[k for k in range(0,K+1,2)]; v={k:[0]*(R+1) for k in Ks}
    for k in Ks: v[k][0]=1 if k==0 else 0
    for mv in range(R):
        for k in Ks:
            v[k][mv+1]=sum(comb(k,2*j)*comb(2*j,j)*v[k-2*j][mv] for j in range(k//2+1))
    return v
RMAX=8; v=Bvals(2*RMAX,2*RMAX+4)
E={}
for r in range(1,RMAX+1):
    k=2*r; pts=[(sp.Integer(i),sp.Integer(v[k][i])) for i in range(0,r+4)]
    E[r]=sp.expand(sp.interpolate(pts,m).subs(m,n/2))
# moment->cumulant for symmetric (even) via recursion: kappa_{2r} = mu_{2r} - sum_{j=1}^{r-1} C(2r-1,2j-1) kappa_{2j} mu_{2(r-j)}
mu={r:E[r] for r in E}; kap={}
for r in range(1,RMAX+1):
    s=mu[r]
    for j in range(1,r):
        s=s - sp.binomial(2*r-1,2*j-1)*kap[j]*mu[r-j]
    kap[r]=sp.expand(s)
print("=== kappa_{2r} and degree (linearity) ===")
cr=[]
for r in range(1,RMAX+1):
    p=sp.Poly(kap[r],n); d=p.degree(); c=int(kap[r].coeff(n,1))
    cr.append(c)
    print(f" kappa_{2*r} = {kap[r]}   deg={d}  {'LINEAR c_r='+str(c) if d==1 else '*** NONLINEAR ***'}")
print("\n=== c_r growth vs Wick (2r-1)!! and the MGF coefficient |c_r|/(2r)! (radius of g(t)) ===")
for r in range(1,RMAX+1):
    dfac=1
    for t in range(1,2*r,2): dfac*=t  # (2r-1)!!
    a=abs(cr[r-1])/factorial(2*r)
    print(f" r={r}: c_r={cr[r-1]:>12} | (2r-1)!!={dfac:>8} | |c_r|/(2r-1)!!={abs(cr[r-1])/dfac:7.2f} | |c_r|/(2r)! = {a:.5f}")
print("\nMGF coeff ratios a_{r+1}/a_r (->limit L; g(t) radius=1/sqrt(L); saddle t*~sqrt(2logm/n)->0 so floor needs only g analytic at 0):")
A=[abs(cr[r-1])/factorial(2*r) for r in range(1,RMAX+1)]
for r in range(1,RMAX): print(f"  a_{r+1}/a_{r} = {A[r]/A[r-1]:.4f}")
