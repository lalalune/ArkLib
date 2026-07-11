import math
from fractions import Fraction as Fr

# The EXACT char-0 period law = n-step random walk: eta = sum_{j=0}^{n-1} omega^{a_j} with
# a_j uniform... but precisely E_r^{char0}(mu_n) = zeroSumCount counting = number of 2r-tuples
# (v_1..v_2r) in mu_n^{2r} with v_1+...+v_2r = 0 (negation-closed energy).
# For mu_n = full nth roots of unity (the relevant generic/limit case), this equals
# the constant term [z^0] (sum_{k} z^{?}) ... Standard: E_r(full mu_n) where mu_n = nth roots.
# The 2r-th moment of |S|^2 ... Use the BESSEL law: A_r := E_r^{char0} = (2r)! [x^r] I_0(2 sqrt x)^{n}
#   wait the dyadic uses n/2; for the FULL group of size n the random-walk 2r-moment is
#   E[|sum_{j} e(theta_j)|^{2r}] over n iid uniform phases = sum over matchings = central binomial.
# Let's compute the exact moment M(2r) of W_n = sum of n iid uniform unit phasors:
#   E[|W_n|^{2r}] = sum over (k_1..k_n) multinomial... = integral. Closed form:
#   E[|W_n|^{2r}] = sum_{...} = number of ways to choose for each step ... 
# Known: E[|W_n|^{2r}] = sum_{j} (multinomial)  but simplest: it's the constant term
#   [z^0] (z + z^{-1} + ... )? No. For uniform phases, char fn of one step is J_0-like;
#   E[|W_n|^{2r}] = (r!)^2 * sum_{k_1+..+k_n=r over... } hmm.
# Use the integral / I_0 generating fn:  sum_r E[|W_n|^{2r}] x^r/(r!)^2 = I_0(2 sqrt x)^n.
#   => E[|W_n|^{2r}] = (r!)^2 [x^r] I_0(2 sqrt x)^n.
# I_0(2 sqrt x) = sum_{k>=0} x^k/(k!)^2.  So I_0(2 sqrt x)^n coefficient of x^r:
#   [x^r] = sum_{k_1+...+k_n = r} prod 1/(k_i!)^2.
# Then moment A_r := E[|W_n|^{2r}] = (r!)^2 * that.   (matches Bessel law with exponent n)

def coeff_I0pow(n, r):
    # [x^r] (sum_k x^k/(k!)^2)^n  as exact Fraction
    # dp over n factors
    # poly = list of Fraction coeffs index 0..r
    base = [Fr(1, math.factorial(k)**2) for k in range(r+1)]
    poly = [Fr(0)]*(r+1); poly[0]=Fr(1)
    for _ in range(n):
        new=[Fr(0)]*(r+1)
        for i in range(r+1):
            if poly[i]==0: continue
            for k in range(r+1-i):
                new[i+k]+=poly[i]*base[k]
        poly=new
    return poly[r]

def A_r(n, r):
    return Fr(math.factorial(r))**2 * coeff_I0pow(n, r)

def dfact_odd(r):
    v=Fr(1)
    for j in range(1,r+1): v*= (2*j-1)
    return v

print("EXACT char-0 random-walk period law W_n (sum of n uniform unit phasors)")
print("m_r = A_r / ((2r-1)!! n^r);  Wick-normalized.  R(r)=m_{r+1}/m_r")
for n in [4,8,16,32,64,128]:
    rmax = 18
    ms=[]
    for r in range(0, rmax+1):
        if r==0: ms.append(Fr(1)); continue
        Ar=A_r(n,r)
        wick=dfact_odd(r)*Fr(n)**r
        ms.append(Ar/wick)
    # R(r) and log-convexity check: m_r^2 <= m_{r-1} m_{r+1} (log-CONVEX) ?
    Rs=[float(ms[r+1]/ms[r]) for r in range(0,rmax)]
    # antitone of R, m_r<=1, log-convex of m
    lc_ok = all(ms[r]*ms[r] <= ms[r-1]*ms[r+1] for r in range(1,rmax))  # log-convex
    lcc_ok= all(ms[r]*ms[r] >= ms[r-1]*ms[r+1] for r in range(1,rmax)) # log-concave
    mle1 = all(ms[r]<=1 for r in range(0,rmax+1))
    Rmono_dec = all(Rs[r+1]<=Rs[r]+1e-15 for r in range(0,len(Rs)-1))
    print(f"n={n:4d}: m1={float(ms[1]):.4f} m2={float(ms[2]):.4f} m_r<=1?{mle1}  logCONVEX?{lc_ok} logconcave?{lcc_ok}  R-antitone?{Rmono_dec}")
    print(f"        R(r): "+" ".join(f"{Rs[r]:.4f}" for r in range(min(10,len(Rs)))))
    print(f"        m_r : "+" ".join(f"{float(ms[r]):.4f}" for r in range(min(10,len(ms)))))
