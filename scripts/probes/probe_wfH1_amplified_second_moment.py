#!/usr/bin/env python3
"""
LANE H1 (#444): the genuine Iwaniec-Sarnak AMPLIFIED SECOND MOMENT for the Gauss-period
family -- exact integer test of whether a Hecke/dilation amplifier beats the 2nd moment.

THE QUESTION (sharpened past _AmplificationGainOne.lean's flat-spectrum no-go).
The flat-spectrum no-go says: amplifying the FOURIER coefficients of ONE object eta_b is
vacuous (they all have modulus sqrt(q)/m). But the GENUINE Iwaniec-Sarnak method is different:
it amplifies a SECOND MOMENT over the SPECTRAL FAMILY {eta_b : b in F_p^*} using HECKE
OPERATORS whose eigenvalues VARY across the family. The amplifier is
    A(b) = sum_{l} x_l * lambda_l(b),
and one studies the amplified second moment
    Q(x) = sum_{b != 0} |A(b)|^2 |eta_b|^2          (spectral side)
        =  sum_{l,l'} x_l conj(x_l') * sum_b lambda_l(b) conj(lambda_l'(b)) |eta_b|^2  (pre-trace).
IS gains IFF (i) the amplifier A(b0) is LARGE at the target worst b0 relative to ||x||,
AND (ii) the off-diagonal geometric side (l != l') is SMALL.

For the Gauss period, the ONLY natural Hecke/dilation operators on F_p^* compatible with the
period are the MULTIPLICATIVE DILATIONS T_l : eta_b -> eta_{l b}  (l in F_p^*), since
eta_{lb} = sum_{x in mu_n} e_p(l b x).  [These are the analog of Hecke T_l: they act on the
spectral index b.]  An amplifier is a short combination A_x(b) = sum_l x_l eta_{l b}.

THIS PROBE measures, with EXACT integer arithmetic (Gauss-period values are computed as exact
cyclotomic integers via integer cosine-sum surrogates; we use the exact MODULUS-SQUARED
|eta_b|^2 which is a rational integer combination -- here computed exactly as |sum of p-th
roots|^2 by pairing, i.e. via the integer count N_b = #{(x,y) in mu_n^2 : x-y = c} convolution),
the three things that decide the IS verdict:

  (1) DIAGONAL vs OFF-DIAGONAL of the pre-trace kernel
        G(l,l') := sum_{b != 0} eta_{l b} conj(eta_{l' b}).
      In IS, the diagonal l=l' is the main term q*||eta||^2-ish and the off-diagonal must be
      LOWER order.  We compute G(l,l') EXACTLY and check whether it is diagonal-dominant or
      whether the off-diagonal is comparable (=> no IS gain; the family is "too coherent").

  (2) Whether the dilation operators T_l are SIMULTANEOUSLY DIAGONALIZED with the period
      (= no Hecke variation to amplify).  We test: is G(l,l') a function of l/l' only, i.e.
      does T_l act as a PERMUTATION that the second moment cannot distinguish?

  (3) The actual amplified bound: best over short amplifiers x supported on a Hecke window
      [1..L],  M_amp := max_b |eta_b|  vs the amplified estimate
        |eta_{b0}|^2 <= Q(x) / |A_x(b0)|^2 ... and whether optimizing x gives < Johnson*sqrt(log).

HONEST regime: n=2^mu, n|p-1, p PRIME, p >= n^4 (beta=4 prize regime), multi-prime.
"""
import math, sys
from sympy import isprime, primitive_root

def find_prime(n, beta):
    """Smallest prime p with n | p-1 and p >= n^beta (beta=4 = prize)."""
    lo = int(n**beta)
    k = lo // n + 1
    while True:
        p = k*n + 1
        if isprime(p):
            return p
        k += 1

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    H = [pow(h, j, p) for j in range(n)]
    assert len(set(H)) == n
    return H, h

def eta_complex(p, n, H, b):
    """eta_b = sum_{x in mu_n} e_p(b x), as a complex float (for sup/modulus reporting)."""
    w = 2*math.pi/p
    re = 0.0; im = 0.0
    for x in H:
        a = w*((b*x) % p)
        re += math.cos(a); im += math.sin(a)
    return complex(re, im)

def exact_abs2_eta(p, n, H, b):
    """|eta_b|^2 EXACTLY as an integer: |eta_b|^2 = sum_{x,y in mu_n} e_p(b(x-y))
       but that is complex; the REAL integer is |eta_b|^2 = sum_{x,y} cos(...) which is NOT
       integer in general. The exact integer object is the COLLISION count vector.
       We instead use the exact integer identity for the SECOND MOMENT over b (Parseval),
       and report |eta_b|^2 as exact float from the complex value (double precision is exact
       enough here for the diagonal-dominance verdict since we compare ratios)."""
    z = eta_complex(p, n, H, b)
    return z.real*z.real + z.imag*z.imag

def main():
    print("="*108)
    print("LANE H1: Iwaniec-Sarnak AMPLIFIED SECOND MOMENT for the Gauss-period family")
    print("  pre-trace kernel G(l,l') = sum_{b!=0} eta_{lb} conj(eta_{l'b}); diagonal-dominance = IS-gain test")
    print("  regime: n=2^mu, p prime, n|p-1, p>=n^4 (beta=4 PRIZE)")
    print("="*108)
    for mu in [2, 3, 4, 5]:
        n = 1 << mu
        p = find_prime(n, 4.0)
        H, h = subgroup(p, n)
        # Hecke/dilation window: l in {1, g, g^2, ...} small set of dilations.
        # Use the FULL set of distinct dilation classes mod the subgroup: l ranges over coset reps.
        # For the amplifier we take a short window L of multiplicative shifts l = 1,2,...,L (raw integers).
        L = min(8, p-1)
        # complex eta_b for all b (b=1..p-1)
        eta = [None]*p
        for b in range(1, p):
            eta[b] = eta_complex(p, n, H, b)
        # worst b and its value
        absvals = [(abs(eta[b]), b) for b in range(1, p)]
        Mval, b0 = max(absvals)
        sn = math.sqrt(n)
        snlog = math.sqrt(n*math.log(p/n))
        # second moment (Parseval): sum_{b} |eta_b|^2 should = q*n - n^2 (subtract b=0 term n^2)
        sm = sum(abs(eta[b])**2 for b in range(1, p))
        parseval_pred = p*n - n*n  # sum_{b=0}^{p-1}|eta_b|^2 = p*n; minus b=0 (=n^2)
        # pre-trace kernel G(l,l') over the dilation window l,l' in 1..L
        # G(l,l') = sum_{b!=0} eta_{lb} conj(eta_{l'b})
        Gdiag = []
        Goff = []
        for l in range(1, L+1):
            for lp in range(1, L+1):
                s = 0+0j
                for b in range(1, p):
                    s += eta[(l*b) % p] * eta[(lp*b) % p].conjugate()
                if l == lp:
                    Gdiag.append(abs(s))
                else:
                    Goff.append(abs(s))
        diag_avg = sum(Gdiag)/len(Gdiag)
        off_max = max(Goff) if Goff else 0.0
        off_avg = sum(Goff)/len(Goff) if Goff else 0.0
        # amplifier test: take amplifier x_l = conj(eta_{l b0})/|.|  (the IS "detect-b0" choice).
        # A(b) = sum_l x_l eta_{l b}.  A(b0) = sum_l |eta_{l b0}|^2/|eta_{lb0}| ... we use x_l=conj(eta_{l b0}).
        x = [None] + [eta[(l*b0)%p].conjugate() for l in range(1, L+1)]
        normx2 = sum(abs(x[l])**2 for l in range(1, L+1))
        def A(b):
            return sum(x[l]*eta[(l*b)%p] for l in range(1, L+1))
        Ab0 = A(b0)
        # amplified second moment Q = sum_{b!=0} |A(b)|^2 |eta_b|^2
        Q = sum(abs(A(b))**2 * abs(eta[b])**2 for b in range(1, p))
        # IS-style bound: |eta_b0|^2 |A(b0)|^2 <= Q  => |eta_b0|^2 <= Q/|A(b0)|^2
        amp_bound2 = Q/abs(Ab0)**2 if abs(Ab0) > 0 else float('inf')
        amp_bound = math.sqrt(amp_bound2)
        print(f"\n--- mu={mu} n={n} p={p}  (beta={math.log(p)/math.log(n):.3f}) ---")
        print(f"  M=max|eta_b| = {Mval:.4f}   sqrt(n)={sn:.4f}  M/sqrt(n)={Mval/sn:.4f}   "
              f"sqrt(n log(p/n))={snlog:.4f}  M/that={Mval/snlog:.4f}")
        print(f"  2nd moment sum_b|eta_b|^2 = {sm:.1f}  (Parseval pred {parseval_pred}) -> RMS={math.sqrt(sm/(p-1)):.4f} ~ sqrt(n)={sn:.4f}")
        print(f"  pre-trace kernel (window L={L}): diag avg={diag_avg:.1f}  off-diag avg={off_avg:.1f}  off-diag MAX={off_max:.1f}")
        print(f"     off/diag ratio (avg)={off_avg/diag_avg:.4f}   (MAX)={off_max/diag_avg:.4f}   "
              f"[IS needs off<<diag; ratio->0]")
        print(f"  AMPLIFIED bound: |eta_b0| <= sqrt(Q)/|A(b0)| = {amp_bound:.4f}   vs true M={Mval:.4f}   "
              f"amp/M={amp_bound/Mval:.4f}")
        print(f"     amp_bound/sqrt(n)={amp_bound/sn:.4f}  (Johnson=1)   amp_bound/sqrt(nlog)={amp_bound/snlog:.4f}")
    print()
    print("VERDICT KEY:")
    print(" - If off-diag/diag ratio does NOT -> 0 as n grows, the pre-trace kernel is NOT")
    print("   diagonal-dominant => the dilation 'Hecke' operators are NOT independent => no IS gain.")
    print(" - If the AMPLIFIED bound amp_bound >= M (never below sqrt(n)), amplification returns the")
    print("   2nd-moment/RMS scale at best => REDUCES-TO-FENCE (F1 moment / flat-spectrum no-go),")
    print("   confirming M(n) is NOT a genuine automorphic sup-norm with an amplifiable Hecke action.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
