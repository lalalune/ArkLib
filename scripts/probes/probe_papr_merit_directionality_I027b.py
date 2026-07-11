"""
IDEA [I027] DECISIVE DIRECTIONALITY TEST.

The literature identity (Jedwab survey; Borwein-Lockhart):
    || sum_j s_j z^j ||_4^4 = N^2 * (1 + 1/F),     F = merit factor.
=> bounded merit factor F=Theta(1)  <=>  L4 norm is at the floor  ~ N^{1/2}.
The merit factor controls the L4 (4th-moment) flatness of the spectrum.

Our object M(mu_n) is an L-INF quantity of the SAME spectral vector whose L4-flatness
the dual merit factor controls. The idea claims an L4 -> L-inf interpolation costing
only sqrt(log m). This probe tests, over PROPER mu_n (p prime, p>>n^3, m=(p-1)/n>1):

  (A) L2(eta), L4(eta), Linf(eta)=M  of the COSET spectrum.
  (B) the merit-factor-style quantity  F_periodic = (sum|eta|^2)^2 / (sum|eta|^4 - mean^2 ...)
      i.e. whether the *periodic* 4th moment is flat (Theta of floor).
  (C) THE DUALITY DIRECTION: does Linf <= L4 * sqrt(log m) hold from ABOVE
      (the claimed inequality), or is Linf >> L4 (the gap is a power of n)?
  (D) report  Linf / (L4 * sqrt(log m))  -- the claimed bound is this ratio <= ~1.

Smaller p (p ~ n^3.05) so we can push n high; honesty floor p>>n^3 still met.
"""
import math, numpy as np
from sympy import isprime, primitive_root

def spectrum(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] = 1.0; x = (x*h) % p
    F = np.fft.fft(ind)
    a = np.abs(F); a[0] = 0.0
    m = (p-1)//n
    eta = np.array([a[pow(g, j, p)] for j in range(m)], dtype=float)  # one rep per coset
    return eta, m

print(" n     p          m       L2      L4      Linf=M   L4/L2   Linf/L2  Linf/(L4*sqrt(log m))  4thMom/floor")
ns=[]; lnMs=[]
for a in range(3, 13):
    n = 2**a
    p = max(int(round(n**3.05)), n*n*n+3)
    while not ((p-1)%n==0 and isprime(p) and (p-1)//n > 1):
        p += 1
    if p > 120_000_000:
        print(" n=%d p=%d too large"%(n,p)); break
    eta, m = spectrum(n, p)
    L2 = math.sqrt((eta**2).mean())          # rms over cosets
    L4 = ((eta**4).mean())**0.25
    Linf = eta.max()
    # periodic 4th-moment flatness: ratio of mean(|eta|^4) to (mean|eta|^2)^2 (=1 iff perfectly flat)
    fourth_ratio = (eta**4).mean() / ((eta**2).mean()**2)
    slm = math.sqrt(max(math.log(m),1e-9))
    claimed = Linf/(L4*slm) if L4*slm>0 else float('nan')
    ns.append(a); lnMs.append(math.log(Linf)/math.log(n))
    print(" %4d  %-10d %-7d %7.3f %7.3f %8.3f %7.3f %8.3f  %18.4f   %10.4f"
          %(n,p,m,L2,L4,Linf,L4/L2,Linf/L2,claimed,fourth_ratio))

if len(ns)>=3:
    A=np.vstack([np.ones(len(ns)),np.array(ns)]).T
    logM=[lm*nn for lm,nn in zip(lnMs,ns)]
    sol,_,_,_=np.linalg.lstsq(A,np.array(logM),rcond=None)
    print("\n effective exponent alpha (M ~ n^alpha): %.3f  [floor 0.5 ; L2-rms exponent 0.5]"%sol[1])
    print(" NOTE: if L4/L2 stays Theta(1) (4thMom/floor bounded) but Linf/L2 grows like n^c,")
    print("       then L4-flatness (=bounded merit) does NOT control Linf=M: the duality is the WRONG direction.")
