import math
def i0(z):
    s=0.0;t=1.0;k=0
    while t>1e-18*max(s,1) or k<5:
        s+=t;k+=1;t=(z/2)**(2*k)/(math.factorial(k)**2)
        if k>400:break
    return s
# the relaxation throws away  I₀(2y)^{n/2} vs e^{n y²/2}.  Gap ratio at the optimal y's:
print("at optimal-y region: I₀(2y)^{n/2} vs e^{ny²/2}  (ratio<1 = relaxation is lossy)")
for n in [8,16,32]:
    for y in [0.5,1.0,1.3,1.5,1.7]:
        exact=i0(2*y)**(n/2)
        gauss=math.exp(n*y*y/2)
        print(f"  n={n} y={y}: I₀(2y)^(n/2)={exact:.4g}  e^(ny²/2)={gauss:.4g}  ratio={exact/gauss:.4f}")
    print()
# the exact bound min_y arcosh(p·I₀(2y)^{n/2})/y vs gaussian min_y arcosh(p·e^{ny²/2})/y
print("CORE bounds (p=40961,n=8,floor=11.69): exact-Bessel vs gaussian-relaxation")
p=40961;n=8
import numpy as np
beE=1e9;beG=1e9
for y in np.linspace(0.05,2.5,500):
    beE=min(beE, math.acosh(p*i0(2*y)**(n/2))/y)
    beG=min(beG, math.acosh(p*math.exp(n*y*y/2))/y)
print(f"  exact-Bessel bound={beE:.3f}  gaussian-relax bound={beG:.3f}  floor=11.69")
