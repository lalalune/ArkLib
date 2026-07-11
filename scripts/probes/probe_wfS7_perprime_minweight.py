#!/usr/bin/env python3
# wf-S7 (#444): the char-p Mann analogue, PER-PRIME — the minimal SPURIOUS weight w_min(p).
#
# THE SHARP QUESTION (Mann char-p analogue).  Char-0 Mann classification: for n=2^mu the only
# minimal vanishing +-1 sums of n-th roots are ANTIPODAL pairs (zeta^i - zeta^{i+n/2} = 0),
# weight 2.  These vanish over Z, so are NOT spurious (the char-0 energy already counts them).
# The char-p analogue: FIX a prize prime p = 1 mod n (n=2^mu), p ~ n^4 odd.  A *spurious* config
# is a +-1 sum sigma_T of n-th roots with N(sigma_T) != 0 over Z but p | N(sigma_T).  Define
#     w_min(p) := min { weight(T) : sigma_T NOT antipodal-balanced, p | N(sigma_T) }.
# If w_min(p) is BOUNDED BELOW by an absolute-or-slow function (a char-p Mann floor), then the
# spurious relations all have large weight and their count is controlled => K bounded.
#
# DISTINCT FROM probe_wfS7_minnorm_growth (which computes maxOdd over ALL weight-w configs).
# Here p is FIXED first; we find the SMALLEST weight at which p divides SOME nonzero norm.
# This is exactly the char-p Mann minimal-spurious-relation weight.
#
# We also record, at that minimal weight, HOW MANY distinct supports realize it (the count that
# feeds spur_r), and whether p | N forces a structured (e.g. coset / fixed-difference) support.

import itertools, sys, math
from sympy import cyclotomic_poly, resultant, symbols, Poly, isprime

x = symbols('x')

def prize_primes(n, count, lo_frac=0.5, hi_frac=4.0):
    p4 = n**4
    out, k = [], 1
    while len(out) < count:
        c = 1 + k*n
        if c >= int(p4*lo_frac) and isprime(c):
            out.append(c)
        k += 1
        if c > p4*hi_frac:
            break
    return out

def is_antipodal_balanced(support, signs, n):
    # antipodal vanishing piece: for each i, +zeta^i and -zeta^{i+n/2} cancel.
    # check whether the config is a disjoint union of antipodal cancelling pairs (=> N=0 anyway)
    half = n//2
    d = {pos: s for pos, s in zip(support, signs)}
    used = set()
    for pos in support:
        if pos in used: continue
        anti = (pos + half) % n
        if anti in d and d[anti] == -d[pos]:
            used.add(pos); used.add(anti)
    return len(used) == len(support) and len(support) % 2 == 0

def min_spur_weight(n, p, wmax):
    """smallest weight w s.t. p | N(sigma_T) for some nonzero-norm config; return (w, witnesses)."""
    Phi = Poly(cyclotomic_poly(n, x), x)
    positions = list(range(n//2))  # half range suffices (zeta^{i+n/2}=-zeta^i)
    for w in range(2, wmax+1):
        hits = []
        for support in itertools.combinations(positions, w):
            for tail in itertools.product((1,-1), repeat=w-1):
                signs = (1,)+tail
                P = Poly(sum(s*x**pos for s,pos in zip(signs,support)), x)
                N = int(resultant(Phi, P))
                if N != 0 and N % p == 0:
                    hits.append((support, signs, N))
        if hits:
            return w, hits
    return None, []

def main():
    n = int(sys.argv[1]) if len(sys.argv)>1 else 16
    wmax = int(sys.argv[2]) if len(sys.argv)>2 else (n//2)
    nprimes = int(sys.argv[3]) if len(sys.argv)>3 else 5
    primes = prize_primes(n, nprimes)
    band = round(2*4*math.log(n))  # 2r ~ 2 ln(n^4) -- prize depth window
    print(f"== wf-S7 PER-PRIME char-p Mann analogue, n={n} (=2^{int(math.log2(n))}), p~n^4={n**4} ==")
    print(f"   prize depth band 2r ~ 2 ln(n^4) = {band}; if w_min(p) >> band the char-0 transfer holds at depth\n")
    print(f"   {'p':>10} {'p mod n':>8} {'w_min(p)':>9} {'#witnesses@wmin':>16} {'note':>20}")
    rows=[]
    for p in primes:
        w, hits = min_spur_weight(n, p, wmax)
        if w is None:
            print(f"   {p:>10} {p%n:>8} {'>'+str(wmax):>9} {'0':>16} {'NO spur <= wmax':>20}")
            rows.append((p, None))
            continue
        # dedup supports (ignoring sign, just to count distinct supports)
        supports = set(h[0] for h in hits)
        # any structured? all-coset-of-fixed-difference check (cheap heuristic): constant gap
        note=""
        for s,si,N in hits[:1]:
            note=f"e.g.{s}"
        print(f"   {p:>10} {p%n:>8} {w:>9} {len(hits):>16} {note:>20}")
        rows.append((p, w))
    print()
    ws=[w for _,w in rows if w is not None]
    if ws:
        print(f"   w_min over tested primes: min={min(ws)} max={max(ws)} ; depth band 2r={band}")
        if min(ws) <= band:
            print(f"   *** w_min <= depth band: SHORT spurious relations EXIST at prize depth -> Mann floor does NOT save transfer at these (sub-prize) n.")
        else:
            print(f"   *** w_min > depth band: no short spurious relation reaches prize depth here.")

if __name__=="__main__":
    main()
