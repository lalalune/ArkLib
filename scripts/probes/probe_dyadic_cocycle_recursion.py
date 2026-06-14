#!/usr/bin/env python3
"""
probe(#389): the 2-adic FFT-butterfly recursion for the dyadic subgroup character sum, and an
HONEST transfer-cocycle reframing of the open sup-norm core.

Let S_k(t) = sum_{j=0}^{2^k-1} e_p(t * zeta^j),  zeta = primitive 2^k-th root of unity in F_p.
This is the character sum whose SUP over t is the prize's open core (the L^infty Shaw error; the
average is sqrt(n) by Parseval, the sup is conjecturally <= C sqrt(n log n) but unproven for
n = p^{1/5}, far below Weil's sqrt(q) and only n^{1-nu} from BGK).

VERIFIED IDENTITY (this probe, errors ~1e-15):
    S_k(t) = S_{k-1}(t) + S_{k-1}(t * zeta_k)          [the FFT butterfly on mu_{2^k}]
because mu_{2^k} = mu_{2^{k-1}}  (union)  zeta_k * mu_{2^{k-1}}  (even/odd cosets, DISJOINT), so the
L^2 cross-term Sum_t S_{k-1}(t) conj(S_{k-1}(t zeta_k)) = 0 exactly => Parseval avg|S| = sqrt(n).

REFRAMING (an attack surface, NOT a closure): iterating the butterfly expresses the sup growth via a
product of 2x2 transfer matrices, so sup_t|S_k(t)| ~ 2^{k*lambda} with lambda the top Lyapunov
exponent of the transfer cocycle; square-root cancellation <=> lambda = (1/2)log2 (a "non-resonant"
cocycle, the Parseval value).

  *** HONEST CAVEAT (corrects an earlier overstatement). *** This is NOT the Marklof / Cellarosi
  continued-fraction renormalization of incomplete THETA/GAUSS sums. Those have a QUADRATIC phase
  e(n^2 alpha + n beta); their renormalization is driven by the continued fraction of alpha. OUR sum
  is GEOMETRIC in j -- the phase is t*zeta^j with zeta a root of unity, i.e. the dynamics is j -> j+1
  = multiplication by zeta on Z/2^k, NOT a quadratic phase. So the theta-sum machinery does NOT
  directly apply. The transfer-cocycle / Lyapunov picture is a legitimate (Furstenberg-type) FRAMING
  of the SAME open question, but "lambda = (1/2)log2 for this multiplicative cocycle" is precisely the
  square-root-cancellation conjecture for subgroup character sums restated -- still OPEN, with the
  honest tools remaining BGK / sum-product / Stepanov (see deltastar-research-map.md (b)/(ii)).

What is genuinely new/useful here: the EXACT butterfly identity (with the disjoint-coset L^2
orthogonality) is a clean inductive handle a transfer/Lyapunov attack can start from; the
theta-sum analogy is heuristic only, not a reduction.
"""
import sympy, math
import numpy as np

def S(t, p, zeta, n):
    powers = [pow(int(zeta), j, p) for j in range(n)]
    ang = 2*math.pi*np.array([float((t*pw) % p) for pw in powers])/p
    return complex(np.sum(np.exp(1j*ang)))

def main():
    p = 1073741953
    print("Verifying  S_k(t) = S_{k-1}(t) + S_{k-1}(t*zeta_k)  (exact FFT butterfly):")
    for k in (4, 6, 8):
        n = 1 << k
        g = int(sympy.primitive_root(p)); zk = pow(g, (p-1)//n, p); zkm1 = pow(zk, 2, p)
        err = 0.0
        for t in (1, 7, 12345, 999999, p-3):
            lhs = S(t, p, zk, n)
            rhs = S(t, p, zkm1, n>>1) + S(t*zk % p, p, zkm1, n>>1)
            err = max(err, abs(lhs - rhs))
        even = {pow(zkm1, j, p) for j in range(n>>1)}
        odd = {(zk*pow(zkm1, j, p)) % p for j in range(n>>1)}
        print(f"  k={k} n={n}: max|err|={err:.1e}  even/odd-coset disjoint={len(even & odd)==0}")
    print("=> exact identity; open core = top Lyapunov exp of the (multiplicative, NOT theta) transfer")
    print("   cocycle = (1/2)log2, i.e. square-root cancellation for subgroup char sums. STILL OPEN.")

if __name__ == "__main__":
    main()
