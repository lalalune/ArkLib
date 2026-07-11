#!/usr/bin/env python3
# Exact integer probe for char-0 step-ratio monotonicity gaps r=2..7.
# Checks G(r,n)=(2r+3)E_{r+1}(n)^2-(2r+1)E_r(n)E_{r+2}(n) >= 0
# on the one-sweep prize-scale powers n=8..256 used before formalization.
from fractions import Fraction

E = {
  2: lambda n: 3*n**2 - 3*n,
  3: lambda n: 15*n**3 - 45*n**2 + 40*n,
  4: lambda n: 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n,
  5: lambda n: 945*n**5 - 9450*n**4 + 39375*n**3 - 77175*n**2 + 57456*n,
  6: lambda n: 10395*n**6 - 155925*n**5 + 1022175*n**4 - 3534300*n**3 + 6246471*n**2 - 4370520*n,
  7: lambda n: 135135*n**7 - 2837835*n**6 + 26801775*n**5 - 141891750*n**4 + 433726293*n**3 - 708996288*n**2 + 471556800*n,
  8: lambda n: 2027025*n**8 - 56756700*n**7 + 728377650*n**6 - 5439183750*n**5 + 25055875845*n**4 - 69934975110*n**3 + 107438611995*n**2 - 68492499075*n,
  9: lambda n: 34459425*n**9 - 1240539300*n**8 + 20744573850*n**7 - 206963306550*n**6 + 1327347186165*n**5 - 5524263935190*n**4 + 14357763632355*n**3 - 20957471507115*n**2 + 12885585512800*n,
}

def gap(r,n):
    return (2*r+3)*E[r+1](n)**2 - (2*r+1)*E[r](n)*E[r+2](n)

bad=[]
for n in [8,16,32,64,128,256]:
    row=[]
    for r in range(2,8):
        g=gap(r,n)
        row.append((r,g))
        if g < 0:
            bad.append((r,n,g))
    print(f"n={n} min_gap={min(g for _,g in row)} r_gaps_ok={[r for r,g in row if g>=0]}")
if bad:
    print("FAIL", bad)
    raise SystemExit(1)
print("PASS: all exact integer gaps r=2..7 nonnegative on n=8..256")
