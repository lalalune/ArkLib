#!/usr/bin/env python3
"""#407 nvm-dyadic-tower probe — NVM (nonvanishing-minors) of the compressed-Fourier matrix.

Object (Garcia-Karaali-Katz; Diaz Padilla-Ochoa Arango, arXiv:2310.09992):
  index-m subgroup H of F_q^*, |H|=n=(q-1)/m, char chi on H with m extensions phi_i, Gauss sums
  G_i = G(phi_i) (all |G_i|=sqrt q). CFT matrix (up to root-of-unity row/col scaling, which
  preserves minor vanishing) = symmetric M_{a,b}=T_{a+b}, T_j=(1/m) sum_i w^{ij} G_i, w=zeta_m.
  M = (1/m) F diag(G) F^T,  F_{a,i}=w^{a i}.
  NVM property: ALL k x k minors (all I,J subsets, |I|=|J|=k) nonzero.  (=finite-field BMT uncertainty.)
  Proven for index m=2,3; OPEN for larger index. PRIZE regime: m=(q-1)/n=2^128 CONSTANT, large.

Findings (this probe):
  (A) Cauchy-Binet: minor_{I,J} = (1/m^k) sum_{|K|=k} V_{I,K} V_{J,K} prod_{i in K} G_i, where
      V_{I,K} is a generalized Vandermonde at roots of unity (each nonzero). The minor is a SIGNED
      SUM of C(m,k) nonzero terms; cancellation is the open phenomenon.
  (B) k=1 minors = T_j (can resonate near 0). k=m minor = (det F)^2 prod G_i / m^m (NEVER zero).
      The hard NVM conditions are intermediate k, worst at k~m/2.
  (C) The clean 'NVM <=> all T_j != 0' reduction (that solves m=2,3) BREAKS at m=4=2^2 and worsens
      for m=8,16. POWER-OF-2 index is the WORST case, not a helpful tower.
  (D) Tower descent fails: radix-2 butterfly T_j=(1/2)(A_r + w^j B_r), A,B = index-(m/2) sub-tower
      transforms (chi, chi*psi). Vanishing needs resonance A_r = -w^j B_r — a phase the descent
      cannot control. Davenport-Hasse duplication G(chi)G(chi eta)=chi^-2(2)G(eta)G(chi^2) fixes
      moduli sqrt q and a product but leaves the relative phase free (Chebotarev: equidistributed).
"""
import numpy as np, itertools
from sympy import primitive_root, isprime

def gauss_vec(p, m):
    g = primitive_root(p); n = (p-1)//m
    wp = np.exp(2j*np.pi/p); z = np.exp(2j*np.pi/(p-1)); a0 = 1
    def G(ai):
        s = 0j
        for t in range(p-1):
            s += z**(ai*t) * (wp**pow(g, t, p))
        return s
    return np.array([G(a0 + i*n) for i in range(m)])

def cft(p, m):
    G = gauss_vec(p, m); w = np.exp(2j*np.pi/m)
    F = np.array([[w**(a*i) for i in range(m)] for a in range(m)])
    M = (1/m) * F @ np.diag(G) @ F.T
    return G, w, F, M

def min_minor(M, k=None):
    m = M.shape[0]; worst = np.inf; info = None
    ks = range(1, m+1) if k is None else [k]
    for kk in ks:
        for I in itertools.combinations(range(m), kk):
            for J in itertools.combinations(range(m), kk):
                d = abs(np.linalg.det(M[np.ix_(I, J)]))
                if d < worst:
                    worst, info = d, (kk, I, J)
    return worst, info

def main():
    print("(A) Cauchy-Binet decomposition check (m=8,p=17, worst 3x3 minor):")
    G, w, F, M = cft(17, 8)
    I, J, k = (0, 6, 7), (0, 1, 2), 3
    direct = np.linalg.det(M[np.ix_(I, J)])
    cb = 0j
    for K in itertools.combinations(range(8), k):
        VIK = np.linalg.det(np.array([[w**(a*i) for i in K] for a in I]))
        VJK = np.linalg.det(np.array([[w**(a*i) for i in K] for a in J]))
        cb += VIK * VJK * np.prod([G[i] for i in K])
    cb /= 8**k
    print(f"    direct={direct:.6f}  cauchy-binet={cb:.6f}  match={abs(direct-cb)<1e-8}")

    print("\n(B,C) per-index: worst minor location + whether it drops below the T-floor:")
    for m in [2, 3, 4, 5, 6, 7, 8, 16]:
        cnt = 0
        for p in range(7, 400):
            if not isprime(p) or (p-1) % m:
                continue
            G, w, F, M = cft(p, m)
            T = np.array([(1/m)*sum(w**(i*j)*G[i] for i in range(m)) for j in range(m)])
            minT = np.min(np.abs(T))
            mn, info = min_minor(M)
            below = "  <-- worst is k=%d (below T-floor)" % info[0] if info[0] != 1 and mn < 0.7*minT else ""
            print(f"  m={m} p={p}: minT={minT:.3f} min_minor={mn:.4f} at k={info[0]}{below}")
            cnt += 1
            if cnt >= 2:
                break

    print("\n(D) tower butterfly resonance: min_r,p ||A_r|-|B_r||/sqrt(p) (small => T near 0):")
    for m in [4, 8, 16, 32]:
        mn = np.inf
        cnt = 0
        for p in range(7, 5000):
            if not isprime(p) or (p-1) % m:
                continue
            G = gauss_vec(p, m)
            A = np.fft.fft(G[0::2]); B = np.fft.fft(G[1::2])
            mn = min(mn, np.min(np.abs(np.abs(A)-np.abs(B)))/np.sqrt(p))
            cnt += 1
            if cnt >= 12:
                break
        print(f"  m={m}: {mn:.4f}")

if __name__ == "__main__":
    main()
