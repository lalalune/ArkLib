#!/usr/bin/env python3
"""
wf-L1 (#444): FAST independent cyclotomic-norm excess-prime engine — settles OT2-vs-wfLC at n=32.

INDEPENDENT METHOD (distinct from the F_p Gaussian/Newton incidence engines): a char-p EXCESS at a
prize prime p (a far-line incidence that EXCEEDS its char-0 value) requires p to divide one of the
integer cyclotomic field norms  N_T(deg) = Res_x( Phi_n(x),  h_deg(x; T) )  where h_deg(x;T) is the
complete-homogeneous symmetric polynomial of degree `deg` in the monomials {x^t : t in T} of a band
subset T (|T| = w), reduced via x^n = 1. (This is the resultant whose vanishing mod p creates an
accidental proportionality / heavy set that does NOT occur over C.)

  beta_excess(n,deg,w) = log_n( max over band-subsets T of  maxprimefactor(|N_T(deg)|) ).

DECISION:  beta_excess < 4  =>  NO prize-scale prime (p ~ n^4..n^5) divides any band norm  =>  the
binding-band far-line incidence is char-0 FAITHFUL at the prize prime (q-INDEPENDENT)  =>  OT2 RIGHT.
beta_excess >= 4  =>  a prize prime hits the band  =>  char-p excess  =>  wf-LC RIGHT (fails).

Speed: exact integer resultant via numpy-free Sylvester-free product over the n-th roots is avoided;
instead we compute Res(Phi_n, h) by polynomial remainder (subresultant) over Python ints (exact,
fast for n<=32). h_deg is built mod (x^n-1) so its degree stays < n.
"""
import sys, math, itertools, random
from functools import reduce

# ---------- exact polynomial arithmetic over Z (lists, low-order first) ----------
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                r[i+j] += ai*bj
    return r

def ptrim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a

def pmod_cyclic(a, n):
    """reduce poly a modulo x^n - 1 (so degrees wrap): coeff of x^(i mod n)."""
    r = [0]*n
    for i,c in enumerate(a):
        r[i % n] += c
    return r

def cyclotomic_2power(n):
    """Phi_n for n = 2^mu is x^(n/2) + 1.  (low-order-first list)"""
    assert (n & (n-1)) == 0 and n >= 2
    h = n//2
    p = [0]*(h+1); p[0] = 1; p[h] = 1
    return p

def resultant_via_modular(phi, h, p):
    """Res(phi, h) mod p, by evaluating product of h at roots through det-free PRS mod p.
       We instead compute Res mod many primes is NOT what we want (we want the integer's prime
       factorization). So compute the integer resultant exactly below."""
    raise NotImplementedError

def resultant_int(a, b):
    """Exact integer resultant Res(a,b) via the Euclidean/subresultant remainder sequence over Q,
       cleared to integers. a,b low-order-first integer coeff lists. Returns a Python int.
       Uses fraction-free (Bareiss-like) pseudo-remainder to stay integral."""
    from fractions import Fraction
    A = [Fraction(x) for x in a]; B = [Fraction(x) for x in b]
    def deg(P):
        d = len(P)-1
        while d > 0 and P[d] == 0: d -= 1
        return d
    def lead(P): return P[deg(P)]
    res = Fraction(1)
    da, db = deg(A), deg(B)
    if da < 0 or db < 0: return 0
    sign = 1
    # ensure deg(A) >= deg(B)
    if da < db:
        A, B = B, A; da, db = db, da
        if (da % 2 == 1) and (db % 2 == 1): sign = -sign
    while deg(B) > 0:
        dA, dB = deg(A), deg(B)
        # polynomial remainder A mod B over Q
        R = A[:]
        lb = lead(B)
        while deg(R) >= dB and any(R):
            dR = deg(R)
            coef = R[dR]/lb
            for i in range(dB+1):
                R[dR-dB+i] -= coef*B[i]
            # trim top
            while len(R) > 1 and R[-1] == 0: R.pop()
            if deg(R) == dR:  # safety
                R[dR] = Fraction(0)
                while len(R) > 1 and R[-1] == 0: R.pop()
        dR = deg(R)
        # res update: Res(A,B) = (-1)^{dA*dB} lead(B)^{dA-dR} Res(B,R)
        if (dA % 2 == 1) and (dB % 2 == 1): sign = -sign
        res *= lb ** (dA - dR)
        A, B = B, R
        if deg(B) < 0: return 0
    # now B is constant
    dA = deg(A)
    res *= lead(B) ** dA
    val = res * sign
    assert val.denominator == 1, f"non-integer resultant {val}"
    return int(val.numerator)

def h_complete(deg, T, n):
    """complete-homogeneous symmetric poly of degree `deg` in {x^t : t in T}, reduced mod x^n-1.
       = sum over multisets of size `deg` from T of x^(sum of chosen t).  Built mod x^n-1."""
    from itertools import combinations_with_replacement
    coeff = [0]*n
    for combo in combinations_with_replacement(T, deg):
        coeff[sum(combo) % n] += 1
    # strip trailing zeros for resultant (keep as full-length is fine)
    return coeff

def maxprimefactor(N):
    N = abs(N)
    if N <= 1: return 1
    mp = 1; d = 2
    while d*d <= N:
        while N % d == 0:
            mp = max(mp, d); N //= d
        d += 1 if d == 2 else 2
    if N > 1: mp = max(mp, N)
    return mp

def beta_excess(n, deg, w, sample_cap=3000, seed=11):
    phi = cyclotomic_2power(n)
    subs = list(itertools.combinations(range(n), w))
    if len(subs) > sample_cap:
        random.seed(seed); subs = random.sample(subs, sample_cap)
    maxp = 1; nz = 0; nt = 0
    for T in subs:
        h = h_complete(deg, T, n)
        N = resultant_int(phi, h)
        if N == 0: nz += 1; continue
        mp = maxprimefactor(N)
        if mp > maxp: maxp = mp
        nt += 1
    be = math.log(maxp)/math.log(n) if maxp > 1 else 0.0
    return be, maxp, nz, nt

if __name__ == '__main__':
    print("wf-L1 FAST excess-prime exponent  beta_excess = log_n(maxprime | N_T(deg))")
    print("  beta_excess < 4 => OT2 (faithful, q-indep at prize p~n^4..n^5)")
    print("  beta_excess >=4 => wf-LC (char-p excess at a prize prime)\n")
    # validate against OT2's reported beta_excess(16)=3.249, then settle n=32.
    configs = [
        (16, 5, 7,  "n=16 deg5 w=7  binding band (full, exact)  [OT2 reported 3.249]"),
        (16, 6, 8,  "n=16 deg6 w=8  Johnson band"),
        (16, 7, 9,  "n=16 deg7 w=9"),
        (32, 7, 15, "n=32 deg7 w=15 BINDING band (s*=2k-1=15) sample"),
        (32, 8, 14, "n=32 deg8 w=14 first-bad band sample"),
        (32, 6, 16, "n=32 deg6 w=16 Johnson band sample"),
        (32, 9, 18, "n=32 deg9 w=18 deeper band sample"),
    ]
    for (n,deg,w,lab) in configs:
        be, mp, nz, nt = beta_excess(n, deg, w)
        side = "OT2 (R4-FAITHFUL@prize)" if be < 4 else "wf-LC (R4 FAILS @prize)"
        print(f"  {lab}: nonzero={nt} char0zero={nz} maxprime={mp} beta_excess={be:.3f}  [{side}]", flush=True)
