#!/usr/bin/env python3
"""
probe_407_realizable_bhbi_verify.py  (#407)

Adversarial verification + extension of probe_407_realizable_bhbi.

(V1) EXACT recheck of the n=16 prize-prime INDEPENDENCE: confirm no nonzero {-2..2}^8 relation
     mod 65537, independently (full brute, re-derived omega), and print the count of relations
     at maxC=2 (must be 0) and the minimal height if we extend to maxC=3,4 (to locate where the
     first relation appears -- the realizable C*_real).

(V2) MANY-PRIME sweep at n=16, beta in [3.5, 6]: does realizable independence (no {-2..2} reln)
     hold at EVERY prize-band prime, or is it prime-specific? Prize is forall-field-universal, so a
     single good prime is not enough -- need it to HOLD across the band (rule 5 / c.154 pigeonhole).

(V3) REALIZABILITY CHECK: is the witness g (when it exists) decomposable as a-b with a,b in {-1,0,1}
     AND consistent with disjoint A,B? Any v in {-2..2}^N decomposes as a-b with a,b in {-1,0,1}
     pointwise; verify, and note the disjointness caveat (A,B disjoint signed-point sets).

(V4) THINNESS height curve: C*_real(beta) at n=16 -- minimal height over {-C..C} as beta grows.

(V5) n=32 (N=16) prize-prime spot check via MITM (brute 5^16 too big): is there a {-2..2}^16
     realizable relation at p ~ 32^4? MITM split 8+8.
"""
import sys
from itertools import product

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_2pow_root(p, m):
    n = 1 << m
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    for base in range(2, p):
        r = pow(base, e, p)
        if pow(r, n // 2, p) != 1 and pow(r, n, p) == 1:
            return r
    return None

def powers(omega, N, p):
    return [pow(omega, j, p) for j in range(N)]

def brute_relations_at_height(omega, N, p, h):
    """Count nonzero relations with max|coeff|==h (entries in [-h,h]); return (count, first_witness)."""
    pw = powers(omega, N, p)
    cnt = 0
    first = None
    for g in product(range(-h, h+1), repeat=N):
        mx = max(abs(x) for x in g)
        if mx != h:
            continue
        s = 0
        for j in range(N):
            if g[j]:
                s = (s + g[j]*pw[j]) % p
        if s % p == 0:
            cnt += 1
            if first is None:
                first = g
    return cnt, first

def min_height_full(omega, N, p, maxC):
    for h in range(1, maxC+1):
        c, g = brute_relations_at_height(omega, N, p, h)
        if c > 0:
            return h, g
    return None, None

def min_height_mitm(omega, N, p, maxC):
    """Min height via MITM at each height h (fast for N=8, half=4)."""
    for h in range(1, maxC+1):
        has, g = mitm_has_relation(omega, N, p, h)
        if has:
            return h, g
    return None, None

def mitm_has_relation(omega, N, p, maxC):
    """MITM: split [0,half) and [half,N). enumerate {-maxC..maxC}^half each side; collide
       sum_left = -sum_right. Returns (True, witness) if any nonzero {-maxC..maxC}^N relation."""
    pw = powers(omega, N, p)
    half = N // 2
    rng = range(-maxC, maxC+1)
    left = {}
    for gl in product(rng, repeat=half):
        s = 0
        for j in range(half):
            if gl[j]:
                s = (s + gl[j]*pw[j]) % p
        left.setdefault(s, gl)  # store one rep per residue
    for gr in product(rng, repeat=N-half):
        s = 0
        for j in range(N-half):
            if gr[j]:
                s = (s + gr[j]*pw[half+j]) % p
        need = (-s) % p
        if need in left:
            gl = left[need]
            g = gl + gr
            if any(x != 0 for x in g):
                return True, g
    return False, None

def make_prime_band(m, beta_lo, beta_hi, count):
    n = 1 << m
    out = []
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    base = lo - (lo % n) + 1
    cand = base
    while cand <= hi and len(out) < count:
        if isprime(cand) and (cand-1) % n == 0:
            out.append(cand)
        cand += n
    return out

def realizable_decomp(g):
    """g_j = a_j - b_j with a,b in {-1,0,1}. Return (a,b) pointwise (one valid choice) or None."""
    a = []; b = []
    for v in g:
        if v == 0: a.append(0); b.append(0)
        elif v == 1: a.append(1); b.append(0)
        elif v == -1: a.append(0); b.append(1)
        elif v == 2: a.append(1); b.append(-1)
        elif v == -2: a.append(-1); b.append(1)
        else: return None
    return a, b

def main():
    print("=== V1: n=16 prize-prime p=65537, exact recheck (re-derived omega) ===")
    m = 4; n = 16; N = 8; p = 65537
    omega = primitive_2pow_root(p, m)
    print("  omega=%d  omega^8 mod p=%d (==p-1? %s)" % (omega, pow(omega,8,p), pow(omega,8,p)==p-1))
    for h in (2,3,4):
        c, g = brute_relations_at_height(omega, N, p, h)
        print("  height==%d: #relations=%d  first=%s" % (h, c, g))

    print("\n=== V2: n=16 many-prime band sweep, realizable {-2..2} independence ===")
    band = make_prime_band(4, 3.5, 6.0, 12)
    holds = 0; total = 0
    for p in band:
        om = primitive_2pow_root(p, 4)
        if om is None: continue
        h, g = min_height_full(om, 8, p, 2)
        total += 1
        beta = __import__('math').log(p, 16)
        if h is None:
            holds += 1
            print("  p=%9d beta=%.2f  INDEP up to 2 (chain holds)" % (p, beta))
        else:
            print("  p=%9d beta=%.2f  RELATION h=%d g=%s (chain breaks here)" % (p, beta, h, g))
    print("  => realizable independence holds at %d/%d prize-band primes" % (holds, total))

    print("\n=== V4: thinness height curve C*_real(beta) at n=16 (min height over {-C..C}) ===")
    for beta in (2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 6.0):
        bp = make_prime_band(4, beta, beta+0.4, 1)
        if not bp:
            continue
        p = bp[0]; om = primitive_2pow_root(p, 4)
        if om is None: continue
        h, g = min_height_mitm(om, 8, p, 4)
        bb = __import__('math').log(p, 16)
        print("  beta~%.2f p=%9d  C*_real=%s%s" % (bb, p, h, ("" if h is None else " g=%s"%(g,))))

    print("\n=== V5: n=32 (N=16) prize-prime spot check via MITM ===")
    for beta in (3.0, 4.0, 5.0):
        bp = make_prime_band(5, beta, beta+0.3, 1)
        if not bp: 
            print("  beta~%.1f: no prime found" % beta); continue
        p = bp[0]; om = primitive_2pow_root(p, 5)
        if om is None:
            print("  p=%d no root" % p); continue
        has, g = mitm_has_relation(om, 16, p, 2)
        bb = __import__('math').log(p, 32)
        if has:
            print("  n=32 p=%10d beta=%.2f  REALIZABLE {-2..2} RELATION exists g=%s" % (p, bb, g))
        else:
            print("  n=32 p=%10d beta=%.2f  INDEP up to 2 (chain holds at realizable support)" % (p, bb))

if __name__ == "__main__":
    main()
