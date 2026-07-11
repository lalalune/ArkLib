"""
IDEA [I027]: PAPR <-> merit-factor duality for M(mu_n).

Claim under test:  M(mu_n)/sqrt(n) <= sqrt(1 + log MF_dual)  with MF_dual = Theta(1),
                   giving M = O(sqrt(n log m)).

We test the CHAIN piece by piece on proper 2-power subgroups mu_n of F_p*, p PRIME,
p >> n^3, m = (p-1)/n > 1, NEVER n = p-1.

The spectral vector:  S_b = sum_{x in mu_n} e_p(b x),  b = 0..p-1.
  - S_b depends only on the coset of b in F_p*/mu_n  (S_{b u} = S_b for u in mu_n).
  - So the nonzero spectrum is an m-vector indexed by cosets: eta_j, j=1..m  (plus b=0 -> S=n).
  - M = max_{b!=0} |S_b| = max_j |eta_j|.
  - L2 (Parseval): sum_{b!=0} |S_b|^2 = sum_b |S_b|^2 - n^2 = p*n - n^2 = n(p-n).
    Per coset: each |eta_j|^2 repeated n times over b's; so sum_{j=1..m} n|eta_j|^2 = n(p-n)
    => sum_j |eta_j|^2 = p - n = n(m-1)... wait p-1 = nm so p-n = nm -n +1-1; check below.

We measure:
  M, sqrt(n), M/sqrt(n) = PAPR_root (the L-inf/L2 ratio of the COSET spectrum),
  L4 of coset spectrum: ( (1/m) sum_j |eta_j|^4 )^{1/4} and the "merit-like" ratio,
  and whether M/sqrt(n) tracks sqrt(log m) or grows like a power of n.
"""
import math, numpy as np
from sympy import isprime, primitive_root

def coset_spectrum(n, p):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)          # generator of mu_n
    # indicator of mu_n
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] = 1.0
        x = (x*h) % p
    F = np.fft.fft(ind)              # |F[b]| = |S_b|
    a = np.abs(F)
    a[0] = 0.0
    # collapse to cosets: pick one representative per coset of F_p*/mu_n.
    m = (p-1)//n
    g_pow = [pow(g, i, p) for i in range(p-1)]  # all nonzero elts in cyclic order
    # coset reps: g^0, g^1, ..., g^{m-1} (since mu_n = <g^m>)
    eta = np.array([a[pow(g, j, p)] for j in range(m)])
    return a, eta, m

print(" n     p          m       M         sqrt(n)   M/sqrt(n)  sqrt(log m)  sqrt(1+log m)  alpha_eff")
ns=[]; lnMs=[]
expo = 3.2   # beta in [4,5] ideally but p>>n^3 is the honesty floor; FFT size limits us
for a in range(3,12):
    n = 2**a
    p = max(int(round(n**expo)), n*n*n+1)   # enforce p >> n^3
    while not ((p-1)%n==0 and isprime(p) and (p-1)//n > 1):
        p += 1
    if p > 80_000_000:
        print(" n=%d p=%d too large for FFT"%(n,p)); break
    a_full, eta, m = coset_spectrum(n,p)
    M = a_full.max()
    ratio = M/math.sqrt(n)
    L2_check = (eta**2).sum()           # sum_j |eta_j|^2 should = p-n  (see below)
    ns.append(a); lnMs.append(math.log(M)/math.log(n))
    print(" %4d  %-10d %-7d %9.3f %8.3f  %8.4f   %8.4f     %8.4f      (L2sum=%.0f vs p-n=%d)"
          %(n,p,m,M,math.sqrt(n),ratio, math.sqrt(math.log(m)), math.sqrt(1+math.log(m)), L2_check, p-n))

if len(ns)>=2:
    A=np.vstack([np.ones(len(ns)),np.array(ns)]).T
    logM=[lm*nn for lm,nn in zip(lnMs,ns)]
    sol,_,_,_=np.linalg.lstsq(A,np.array(logM),rcond=None)
    print("\n effective alpha (d log2 M / d log2 n) = %.3f   [prize floor: 0.5; SOTA: 1-o(1)]"%sol[1])
