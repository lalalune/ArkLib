import numpy as np
import sympy

# Adversarial check of MomentCountSupBound docstring claim:
# "The integer-count argument is SHARPER than the per-term ||eta||^{2r} <= sum bound
#  (it uses that a fractional count rounds down to zero)."
# Compare, at FIXED r, the two sup-norm-squared bounds:
#   per-term  :  M^2 <= (sum_b a_b^r)^{1/r}                 [a_b=|eta_b|^2]
#   count     :  M^2 <= inf{ T : sum_b a_b^r < T^r } = (sum_b a_b^r)^{1/r}  (an INFIMUM, not attained)
# The count bound is an OPEN inequality (strict <), inf is the SAME value (sum a^r)^{1/r}.
# So at fixed r the count bound is M^2 <= (sum a^r)^{1/r} as a non-strict closure too.
# Question: does the integer rounding ever give a STRICTLY smaller usable T at fixed r? Only if
# the count can be forced to 0 at a T BELOW (sum a^r)^{1/r}. It cannot: at T just below that value,
# count*T^r <= sum a^r but sum a^r can be >= T^r, so count can be >=1. The inf is exactly (sum a^r)^{1/r}.

def prime_sub(n, beta):
    p = sympy.nextprime(int(n**beta))
    while (p-1) % n != 0:
        p = sympy.nextprime(p)
    return p

def periods(n, p):
    g = sympy.primitive_root(p); h = pow(g,(p-1)//n,p)
    G=set(); x=1
    for _ in range(n):
        G.add(x); x=(x*h)%p
    ind=np.zeros(p)
    for x in G: ind[x]=1.0
    return np.abs(np.fft.fft(ind))

for (n,beta) in [(8,4.0),(16,4.0),(16,3.5)]:
    p=prime_sub(n,beta); mag=periods(n,p); a=mag[1:]**2; M2=a.max()
    print(f"n={n} beta={beta} p={p}  true M^2={M2:.4f}")
    for r in [1,2,3,5,8]:
        ps=(a**r).sum()
        per_term = ps**(1.0/r)            # per-term bound at this r: M^2 <= (sum a^r)^{1/r}
        # count bound smallest provable T at this r: need sum a^r < T^r => T > ps^{1/r}; inf = same
        count_inf = ps**(1.0/r)
        print(f"   r={r}: per-term M^2_bound={per_term:.4f}   count inf T={count_inf:.4f}   equal={np.isclose(per_term,count_inf)}")
