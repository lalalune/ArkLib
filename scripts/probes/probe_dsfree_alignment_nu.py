#!/usr/bin/env python3
# FREE-PROBABILITY alignment test for M(n)=max_{b!=0}|eta_b|, eta_b=sum_{x in mu_n} e_p(bx).
# Question: is the Gauss-sum/period family "asymptotically FREE" (=> Ramanujan, M~2sqrt(n), NO log)
# or "classical/commuting" (=> Gaussian extreme value, M~sqrt(2n log p), the BGK log loss)?
# Computable diagnostics (honest, no lift needed):
#   (R) Ramanujan ratio  M/(2 sqrt n)      -- free predicts ->1 (bounded); if it grows ~sqrt(log p), NOT free.
#   (G) Gaussian ratio   M/sqrt(2 n ln p)  -- classical-independent predicts ->1.
#   (IPR) inverse participation ratio of {|eta_b|^2} = sum|eta_b|^4 / (sum|eta_b|^2)^2 * (p-1)
#         -- =1 for flat (free-like, delocalized), >1 for localized/aligned (eigenvalue clumping).
#   (kurt) excess kurtosis of {eta_b} vs complex Gaussian (free semicircle has NEGATIVE excess kurtosis;
#          classical complex Gaussian has 0; positive => heavy-tailed alignment).
import cmath, math, sympy
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def periods(n,p):
    G=musub(n,p); w=2*math.pi/p
    return [abs(sum(cmath.exp(1j*w*((b*x)%p)) for x in G)) for b in range(1,p)]
print(f"{'n':>5}{'p':>9}{'beta':>6}{'M':>8}{'M/2sqrtn(R)':>12}{'M/sqrt(2n lnp)(G)':>17}{'sqrt(lnp)/2':>11}{'IPR':>7}{'kurt':>8}")
import statistics
for (n,p) in [(8,257),(8,4129),(16,257),(16,4129),(16,65537),(32,4129),(32,40961),(32,1048609),(64,1048609)]:
    if (p-1)%n: continue
    A=periods(n,p)                       # |eta_b|, b=1..p-1
    M=max(A)
    s2=sum(a*a for a in A); s4=sum(a**4 for a in A)
    IPR=s4/(s2*s2)*(p-1)                  # 1=flat(free-like), >1 = aligned/localized
    R=M/(2*math.sqrt(n)); Gr=M/math.sqrt(2*n*math.log(p))
    # excess kurtosis of the real parts? use |eta|^2 distribution normalized
    m2=s2/(p-1); vals=[a*a/m2 for a in A]
    mean=statistics.mean(vals); var=statistics.pvariance(vals)
    kurt=sum((v-mean)**4 for v in vals)/(p-1)/(var*var)-3 if var>0 else 0
    print(f"{n:>5}{p:>9}{math.log(p)/math.log(n):>6.2f}{M:>8.2f}{R:>12.3f}{Gr:>17.3f}{math.sqrt(math.log(p))/2:>11.3f}{IPR:>7.3f}{kurt:>8.2f}")
print()
print("READING: free/Ramanujan => R->const(~1), IPR->1, kurt<0(semicircle). classical => G~1, IPR~?, kurt~0.")
print("if R GROWS ~sqrt(log p)/... and G~const => NOT free, classical-Gaussian-or-worse => BGK log is REAL.")
