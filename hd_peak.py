# THE HD LEVER CRUX: eta over cosets = (1/k) IDFT_k(tau) - 1/k.
# Question: does the Jacobi/HD recursion phase(tau_{2j})=2 phase(tau_j)-phase(J_j) make the 
# IDFT of tau CONCENTRATE (a peak > sqrt(n log), refuting bound) or stay SPREAD (~ sqrt(n log))?
#
# Decompose: the dyadic-index part j (2-power orbit under doubling) carries a quadratic-Gauss-sum-like
# structure. A pure quadratic phase chirp e(c j^2/k) has FLAT IDFT (|IDFT|=const=sqrt(k)) - no peak.
# A linear phase e(c j/k) has a DELTA IDFT (full peak = k). The Gauss sums are in between.
#
# Measure: (1) the IDFT sup of tau (= k*M(n)+1 scale); (2) compare to the IDFT sup of a RANDOM 
# unimodular*sqrt(p) vector (same magnitudes, random phases); (3) compare to a pure LINEAR-phase 
# vector (worst peak) and pure QUADRATIC-phase (flat). Where do the real Gauss sums sit?
import numpy as np
from sympy import primitive_root, nextprime
def taus_of(n,p):
    g=primitive_root(p); k=(p-1)//n
    dlog={}; cur=1
    for a in range(p-1): dlog[cur]=a; cur=cur*g%p
    ep=np.exp(2j*np.pi*np.arange(p)/p)
    dl=np.array([dlog.get(t,0) for t in range(p)])
    taus=np.zeros(k,dtype=complex)
    for j in range(1,k):
        chij=np.exp(2j*np.pi*(j*dl)/k); chij[0]=0
        taus[j]=(chij*ep).sum()
    return taus,k,p
np.random.seed(0)
print("IDFT-sup comparison: real Gauss sums vs random-phase vs linear vs quadratic (all mag sqrt p):")
for ne in [4,5,6,7]:
    n=2**ne
    p=int(nextprime(n*200))
    while (p-1)%(2*n): p=int(nextprime(p))
    taus,k,p=taus_of(n,p)
    sp=np.sqrt(p)
    # set tau_0 = -1 (the formula's -1 sits at all-ones)? Actually formula: eta=(1/k)(-1+IDFT(tau)) with tau_0=0.
    def idft_sup(vec):
        return np.abs(np.fft.fft(vec)).max()
    real_sup=idft_sup(taus)
    # random phases
    rand=np.zeros(k,dtype=complex); rand[1:]=sp*np.exp(2j*np.pi*np.random.rand(k-1))
    rand_sup=np.mean([idft_sup(np.concatenate([[0],sp*np.exp(2j*np.pi*np.random.rand(k-1))])) for _ in range(20)])
    # linear phase: tau_j = sp e(c j /k) -> IDFT delta, sup ~ k sp
    lin=np.zeros(k,dtype=complex); lin[1:]=sp*np.exp(2j*np.pi*0.37*np.arange(1,k)/k)
    lin_sup=idft_sup(lin)
    # quadratic phase
    quad=np.zeros(k,dtype=complex); quad[1:]=sp*np.exp(2j*np.pi*0.37*np.arange(1,k)**2/k)
    quad_sup=idft_sup(quad)
    win=k*np.sqrt(n*np.log(p/n))  # k*M_window
    print(f"  n={n} k={k}: real={real_sup/win:.3f}w  random={rand_sup/win:.3f}w  linear(peak)={lin_sup/win:.2f}w  quad(flat)={quad_sup/win:.3f}w   [w=k*sqrt(n log)]")
