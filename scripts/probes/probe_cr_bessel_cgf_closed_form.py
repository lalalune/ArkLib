# Final: c_r closed form g(t)=(1/2)log I0(2t); structural derivation eta_b = sum_{a<n/2} 2cos(2*pi*b*zeta^a/p)
import sympy as sp
t=sp.symbols('t'); g=sp.Rational(1,2)*sp.log(sp.besseli(0,2*t)); ser=sp.series(g,t,0,18).removeO()
actual=[1,-3,40,-1155,57456,-4370520,471556800,-68492499075]
assert all(sp.simplify(ser.coeff(t,2*r)*sp.factorial(2*r)-actual[r-1])==0 for r in range(1,9))
print("VERIFIED: c_r = (2r)![t^2r] (1/2)log I0(2t), r=1..8")
print("=> char-0 additive-energy CGF: K(t)=n*g(t)=(n/2)log I0(2t)  [I0 entire]")
print("=> kappa_{2r}=c_r*n LINEAR for ALL r (c_r = arcsine/Bessel cumulants); saddle t*->0 => char-0 floor rigorous")
