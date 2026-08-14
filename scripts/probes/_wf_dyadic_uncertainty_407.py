"""
#407 fourier-uncertainty-dyadic angle.

Central claim to TEST (char-0, exact, over C):
  For S a subset of mu_N (N=2^mu), the N-th roots of unity, with weight a=|S|,
  if e_1(S)=...=e_{t-1}(S)=0 (the t-1 consecutive vanishing elementary symmetric fns),
  must S be a union of cosets of mu_t = <zeta_N^{N/t}> ?  (the "rigidity")
  This is what would close the char-0 count.

Equivalently in DFT/uncertainty language:
  Let f = indicator(S) in {0,1}^{Z/N}. Then hat f(j) = sum_{s in S} zeta_N^{-j s_idx}.
  e_t(S) relates to the polynomial prod_{s in S}(X - zeta^s) = X^a - e_1 X^{a-1} + ... .
  Vanishing e_1..e_{t-1} <=> that poly is X^a + (-1)^t e_t X^{a-t} + lower.

We brute-force enumerate ALL S subset of mu_N of each size a, count how many have
e_1=..=e_{t-1}=0, and check whether each such S is mu_t-coset-supported.
N small (8,16,32) so this is feasible for small a.
"""
import itertools, cmath, math
from fractions import Fraction

def esymm_vanishes(idx_set, N, t):
    # elementary symmetric functions e_1..e_{t-1} of {zeta_N^i : i in idx_set}
    # use exact-ish: represent as complex, check |e_j| < tol.
    zeta = [cmath.exp(2j*math.pi*i/N) for i in range(N)]
    pts = [zeta[i] for i in idx_set]
    # Newton / direct via polynomial coefficients
    # build poly coefficients via convolution
    coeffs = [1.0+0j]
    for p in pts:
        new = [0j]*(len(coeffs)+1)
        for k,c in enumerate(coeffs):
            new[k]   += c
            new[k+1] += -p*c
        coeffs = new
    a = len(pts)
    # coeffs[k] = (-1)^k e_k, k=0..a   (coeffs of X^{a-k})
    for j in range(1, t):
        ej = coeffs[j]*((-1)**j)
        if abs(ej) > 1e-7:
            return False
    return True

def is_coset_union(idx_set, N, t):
    # mu_t = { multiples of N/t } if t | N. coset c + (N/t)*<...>: indices form union of
    # arithmetic progressions with common difference N/t.
    if N % t != 0:
        return None  # mu_t not subgroup of mu_N in the clean sense
    step = N//t
    S = set(idx_set)
    # S is union of mu_t-cosets iff closed under +step (mod N)
    for x in S:
        if (x+step)%N not in S:
            return False
    return True

def is_coset_union_gcd(idx_set, N, t):
    # general: <g^t> where g=zeta_N (gen). g^t = zeta_N^t, order = N/gcd(t,N).
    # coset closure under mult by g^t  <=> closed under index shift by +t mod N.
    S = set(idx_set)
    for x in S:
        if (x+t)%N not in S:
            return False
    return True

print("N, a, t : (#vanishing S) | (#coset-union under +t) | (#coset under N/t) | all-coset?")
for N in [8,16]:
    for t in range(2, 6):
        for a in range(t, min(N, t+6)+1):
            cnt=0; coset_t=0; coset_Nt=0; noncoset_examples=[]
            for idx in itertools.combinations(range(N), a):
                if esymm_vanishes(idx, N, t):
                    cnt+=1
                    ict = is_coset_union_gcd(idx, N, t)
                    if ict: coset_t+=1
                    else:
                        if len(noncoset_examples)<5: noncoset_examples.append(idx)
                    icn = is_coset_union(idx, N, t)
                    if icn: coset_Nt+=1
            if cnt>0:
                allc = (coset_t==cnt)
                print(f"N={N:2d} a={a:2d} t={t}: vanish={cnt:4d} | +t-coset={coset_t:4d} | N/t-coset={coset_Nt:4d} | all_+t_coset={allc}")
                if not allc:
                    print(f"        NON-+t-coset examples: {noncoset_examples[:3]}")
