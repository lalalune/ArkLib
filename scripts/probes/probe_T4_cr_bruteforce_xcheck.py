# Independent cross-check: compute E_r^char0 by BRUTE FORCE for small n (n=4,8) at r=1,2,3,
# fit E_r as polynomial in n via the besselCoeff closed form sum_k 1/(k!)^2-style, then
# moment->cumulant, confirm kappa_{2r}=c_r*n with c_r in {1,-3,40}.
import itertools
from math import factorial
def char0_zero_pow2(plus, minus, n):
    half=n//2; coeff=[0]*half
    for a in plus: coeff[a%half]+= (-1 if (a//half)%2 else 1)
    for b in minus: coeff[b%half]-= (-1 if (b//half)%2 else 1)
    return all(c==0 for c in coeff)
def Er(n,r):
    rng=range(n); c=0
    for xs in itertools.product(rng,repeat=r):
        for ys in itertools.product(rng,repeat=r):
            if char0_zero_pow2(xs,ys,n): c+=1
    return c
# E_r should equal (2r)! * [z^r] I0(2*sqrt? ) ... but we just check the moment->cumulant linearity directly
# using two data points (n=4 and n=8) to fit the LINEAR-in-n cumulant.
import sympy as sp
n=sp.symbols('n')
print("Direct brute-force char-0 energies and cumulant linearity check:")
# moments mu_r = E_r / (E_1)... we need normalized even moments. The cumulant recursion used:
# mu[r]=E_r (the raw energy). kappa via kappa_r = mu_r - sum_{j<r} C(2r-1,2j-1) kappa_j mu_{r-j}.
data={}
for nn in [4,8]:
    data[nn]={r:Er(nn,r) for r in [1,2,3]}
    print(f"  n={nn}: E_1={data[nn][1]} E_2={data[nn][2]} E_3={data[nn][3]}")
# fit each E_r as poly in n through both points won't determine cubic; instead trust the
# recursion structure: just verify the cumulant at n=8 minus 2*(n=4) tests linearity slope.
# Simpler: known E_1=n, E_2=2n^2-n, E_3=6n^3-9n^2+4n (standard for negation-pair counting? check)
for nn in [4,8]:
    e1,e2,e3=data[nn][1],data[nn][2],data[nn][3]
    k1=e1
    k2=e2 - 1*k1*e1   # C(3,1)=3? careful: kappa_2 = mu_2 - C(3,1) kappa_1 mu_1? Using the file's recursion:
    # kappa_r = mu_r - sum_{j=1}^{r-1} C(2r-1,2j-1) kappa_j mu_{r-j}
    # r=1: k1=e1.  r=2: k2 = e2 - C(3,1) k1 e1 = e2 - 3 e1^2.  r=3: k3 = e3 - C(5,1)k1 e2 - C(5,3)k2 e1
    k2 = e2 - 3*e1*e1
    k3 = e3 - 5*k1*e2 - 10*k2*e1
    print(f"  n={nn}: kappa_2={k2}  kappa_4(r=2 slot)={k2}  kappa_6(r=3)={k3}   [expect c1*n=n={nn}, c2*n=-3n={-3*nn}, c3*n=40n={40*nn}]")
