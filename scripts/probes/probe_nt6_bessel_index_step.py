from fractions import Fraction as Fr
from math import factorial as fac
def cpow_bessel_exact(m, R):
    bc=[Fr(1,fac(k)**2) for k in range(R+1)]
    c=[Fr(1) if r==0 else Fr(0) for r in range(R+1)]
    for _ in range(m):
        nc=[Fr(0)]*(R+1)
        for r in range(R+1):
            nc[r]=sum(c[i]*bc[r-i] for i in range(r+1))
        c=nc
    return c
# Is there a clean bound (r+1) c_{r+1} <= m c_r  (the ratio claim)?
# Equivalently (r+1) c_{r+1} <= m c_r. Test exactly.
for n in [4,8,16,32,64]:
    m=n//2;R=6
    c=cpow_bessel_exact(m,R)
    print(f"n={n} m={m}: ", end="")
    allok=True
    for r in range(0,R):
        lhs=(r+1)*c[r+1]; rhs=m*c[r]
        ok = lhs<=rhs
        allok = allok and ok
    print("(r+1)c_{r+1} <= m c_r for all r:", allok)
    # diff slack
    for r in range(0,R):
        slack = m*c[r]-(r+1)*c[r+1]
        print(f"     r={r}: m c_r - (r+1) c_{{r+1}} = {float(slack):.4e}  (>=0: {slack>=0})")
