#!/usr/bin/env python3
"""
laneF (#407): the CROSS-PARITY (butterfly cross-term) contribution to the
dyadic Gaussian-period envelope, summed over all frequencies.

Object: H_k = mu_{2^k} (proper subgroup of F_p*), psi_b(x)=omega^{b x} additive char.
period(H,b) = sum_{x in H} psi_b(x).  Butterfly: H_k = H_{k-1} u zeta H_{k-1},
   period(H_k,b) = period(H_{k-1},b) + period(H_{k-1}, b zeta).
Squared:  |P_k(b)|^2 = |P_{k-1}(b)|^2 + |P_{k-1}(b zeta)|^2 + 2 Re( P_{k-1}(b) conj(P_{k-1}(b zeta)) ).

The first two = "even"/Parseval scale.  The CROSS term
   X_k(b) := 2 Re( P_{k-1}(b) conj(P_{k-1}(b zeta)) )
is the cross-parity contribution = the alignment excess delta.

QUESTIONS this probe answers in PRIZE regime (proper subgroup, multi-prime):
 (Q1) sum_{b != 0} X_k(b) = ?   (the AGGREGATE cross-parity -- is it clean / signed?)
 (Q2) sum_{b != 0} |X_k(b)| = ?  vs the diagonal sum_{b!=0}(|P_{k-1}(b)|^2+|P_{k-1}(bz)|^2).
 (Q3) is the cross term confined to O(log n) frequencies b (the imprimitive dirs)?
      i.e. how many b have |X_k(b)| comparable to its max?
 (Q4) the WORST single-b ratio |P_k(b)|^2 / max(|P_{k-1}|^2) -- is the per-level excess bounded?
"""
import cmath, math
from collections import Counter

def prim_root_order(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1:
            return g
    raise RuntimeError("no root of order n")

def subgroup(n, p):
    g = prim_root_order(n, p)
    return [pow(g, j, p) for j in range(n)]

def periods(H, p):
    """period(b) for all b in 0..p-1, as complex."""
    w = 2j * math.pi / p
    P = [0j]*p
    for b in range(p):
        s = 0j
        for x in H:
            s += cmath.exp(w * ((b*x) % p))
        P[b] = s
    return P

def analyze(n, p):
    assert (p-1) % n == 0
    k = n.bit_length()-1            # n = 2^k
    H_k = subgroup(n, p)            # mu_{2^k}
    H_k1 = subgroup(n//2, p)        # mu_{2^{k-1}}
    # zeta of order n with zeta^{n/2} = -1
    g = prim_root_order(n, p)
    zeta = g                        # primitive n-th root; zeta^{n/2} = -1
    P1 = periods(H_k1, p)           # level k-1 periods (length p)
    Pk = periods(H_k, p)            # level k periods

    cross = [0.0]*p
    diag  = [0.0]*p
    for b in range(p):
        bz = (b*zeta) % p
        c = 2.0 * (P1[b] * P1[bz].conjugate()).real
        cross[b] = c
        diag[b] = abs(P1[b])**2 + abs(P1[bz])**2
        # sanity: |Pk(b)|^2 should equal diag+cross
    # verify identity
    maxerr = max(abs(abs(Pk[b])**2 - (diag[b]+cross[b])) for b in range(p))

    nz = list(range(1,p))
    sum_cross   = sum(cross[b] for b in nz)
    sum_abscross= sum(abs(cross[b]) for b in nz)
    sum_diag    = sum(diag[b] for b in nz)
    max_abscross= max(abs(cross[b]) for b in nz)
    # how many b carry >= 50% of max cross (concentration / O(log n)?)
    thr = 0.5*max_abscross
    heavy = sum(1 for b in nz if abs(cross[b])>=thr)
    # worst per-level squared ratio
    maxP1sq = max(abs(P1[b])**2 for b in nz)
    maxPksq = max(abs(Pk[b])**2 for b in nz)
    per_level = maxPksq/maxP1sq if maxP1sq>0 else float('nan')

    print(f"n={n}(=2^{k}) p={p}  p mod n={p%n}")
    print(f"  identity max err           : {maxerr:.3e}  (butterfly square check)")
    print(f"  sum_b X_k(b)   (signed)    : {sum_cross:+.4f}")
    print(f"     theory: sum_b |Pk|^2 - sum_b(diag). sum_b|Pk|^2={sum(abs(Pk[b])**2 for b in nz):.2f}")
    print(f"  sum_b |X_k(b)| (abs)       : {sum_abscross:.4f}")
    print(f"  sum_b diag(b)              : {sum_diag:.4f}    (= 2*(p*n/2 - (n/2)^2)? check)")
    print(f"     Parseval pred 2*( (p-1)*(n/2) ... ): sum_b|P1|^2 over b!=0 = {sum(abs(P1[b])**2 for b in nz):.2f} (should be (p)*(n/2)-(n/2)^2={p*(n//2)-(n//2)**2})")
    print(f"  |sum X| / sum|X|           : {abs(sum_cross)/sum_abscross if sum_abscross>0 else 0:.4f}  (signed cancellation)")
    print(f"  max_b |X_k(b)|             : {max_abscross:.3f};  sqrt scales: sqrt(n)={math.sqrt(n):.2f}, n={n}")
    print(f"  #b with |X|>=0.5 max       : {heavy}  (log2 p={math.log2(p):.1f}, n={n})")
    print(f"  per-level worst |Pk|^2/|P1|^2: {per_level:.4f}  (random=2; excess delta={per_level-2:+.4f})")
    print()

if __name__ == "__main__":
    # PRIZE regime: proper dyadic subgroups, multiple primes p = 1 mod n, p >> n
    for (n,p) in [(8,113),(8,257),(8,401),(16,97),(16,257),(16,353),(32,97),(32,257),(32,673)]:
        if (p-1)%n==0:
            analyze(n,p)
