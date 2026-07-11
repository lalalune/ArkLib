# Lane B4 / W1-MGF obstruction, exact-rational witness extraction for the Lean file.
# W1-MGF:  Phi_nz(y) = sum_r a_r y^{2r}/(2r)!  <=  exp(n y^2/2) = sum_r W_r y^{2r}/(2r)!
#   a_r = (q E_r - n^{2r})/q  (DC-subtracted; = ((q-1)/q) M(r)),  W_r = (2r-1)!! n^r.
# Term-r comparison a_r <= W_r  <=>  q E_r - n^{2r} <= q W_r.
# r=2 (kurtosis): a_2 <= W_2  <=>  q E_2 - n^4 <= 3 n^2 q  <=> q(E_2 - 3n^2) <= n^4.
# At spur prime n=32 p=32993: E_2=3744 (char-0 would be 3n^2-3n=2976).
from fractions import Fraction as F
def df(k):  # (2r-1)!! for k=2r-1
    r=1; i=k
    while i>0: r*=i; i-=2
    return r
for (n,p,E2) in [(32,32993,3744),(32,37217,3360),(32,65537,3360),(32,50177,3360)]:
    q=p
    a2 = F(q*E2 - n**4, q)
    W2 = df(3)*n**2   # 3 n^2
    print(f"n={n} p={p} beta={__import__('math').log(p,n):.3f}: E_2={E2} a_2={float(a2):.2f} W_2={W2} a_2/W_2={float(a2/W2):.4f} a_2>W_2? {a2>W2}")
    # exact integer reduction: q*E2 - n^4 > 3 n^2 q  <=>  q*(E2-3n^2) > n^4
    lhs = q*(E2 - 3*n**2); rhs = n**4
    print(f"   reduction q*(E_2-3n^2)={lhs} vs n^4={rhs}  => a_2>W_2 iff {lhs}>{rhs}: {lhs>rhs}")
