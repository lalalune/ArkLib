#!/usr/bin/env python3
"""ADVERSARIAL AUDIT: independent M3 via the translated PAIR sum, brute pair census.

M3[j1,j2,j3] = q^k * sum over ALL q^{2k} ordered codeword pairs (c,c') of
               [z1^j1 z2^j2 z3^j3] prod_x factor(type of (c(x), c'(x), 0))
with the word-triple (c, c', 0) (translation by the third codeword; the q^k
prefactor is the free choice of p3 — re-derived from scratch for this audit).

Per-coordinate types of (c(x), c'(x), 0) and factors:
  a: c=c'=0      -> z1z2z3 + (q-1)
  b: c=0,  c'!=0 -> z1z3 + z2 + (q-2)   (u=0 agrees with c AND with the 0 word)
  c: c!=0, c'=0  -> z2z3 + z1 + (q-2)
  d: c=c'!=0     -> z1z2 + z3 + (q-2)
  e: else        -> z1 + z2 + z3 + (q-3)

Implementation: NO pencil decomposition, NO weight-distribution formula, NO
triple-counting lemma. Profiles come from popcounts of zero-masks (zero mask of
c - c' gives the equality mask); N(profile) computed by per-coordinate sparse
polynomial DP. Checks: profile-class mass q^{2k}; M3 mass q^(n+3k); S3 symmetry.
Usage: audit_m3_pairs.py q k x1,x2,...
"""
import json
import sys
from itertools import product


def main():
    q = int(sys.argv[1])
    k = int(sys.argv[2])
    domain = sorted(int(t) % q for t in sys.argv[3].split(","))
    n = len(domain)
    assert all(domain) and len(set(domain)) == len(domain)

    # codeword index <-> coefficient tuple; zero masks on D
    coeffs = list(product(range(q), repeat=k))
    m = len(coeffs)
    idx = {cf: i for i, cf in enumerate(coeffs)}
    zmask = [0] * m
    pops = [0] * m
    for i, cf in enumerate(coeffs):
        mk = 0
        for t, x in enumerate(domain):
            acc = 0
            for cc in reversed(cf):
                acc = (acc * x + cc) % q
            if acc == 0:
                mk |= 1 << t
        zmask[i] = mk
        pops[i] = bin(mk).count("1")

    # profile histogram over all ordered pairs
    hist = {}
    for i in range(m):
        ci = coeffs[i]
        zi = zmask[i]
        pi = pops[i]
        for j in range(m):
            zj = zmask[j]
            dcf = tuple((ci[t] - coeffs[j][t]) % q for t in range(k))
            zd = zmask[idx[dcf]]
            a = bin(zi & zj).count("1")
            b = pi - a
            c = pops[j] - a
            d = bin(zd).count("1") - a
            e = n - a - b - c - d
            assert d >= 0 and e >= 0
            kk = (a, b, c, d, e)
            hist[kk] = hist.get(kk, 0) + 1
    assert sum(hist.values()) == q ** (2 * k)

    # N(profile) by per-coordinate DP with the translated factors
    FA = {(1, 1, 1): 1, (0, 0, 0): None}  # constants filled per q below

    def n_poly(profile):
        fa = {(1, 1, 1): 1, (0, 0, 0): q - 1}
        fb = {(1, 0, 1): 1, (0, 1, 0): 1, (0, 0, 0): q - 2}
        fc = {(0, 1, 1): 1, (1, 0, 0): 1, (0, 0, 0): q - 2}
        fd = {(1, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): q - 2}
        fe = {(1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): q - 3}
        P = {(0, 0, 0): 1}
        for f, cnt in zip((fa, fb, fc, fd, fe), profile):
            for _ in range(cnt):
                out = {}
                for (x1, x2, x3), v in P.items():
                    for (d1, d2, d3), w in f.items():
                        kk2 = (x1 + d1, x2 + d2, x3 + d3)
                        out[kk2] = out.get(kk2, 0) + v * w
                P = out
        assert sum(P.values()) == q ** n
        return P

    qk = q ** k
    M3 = {}
    for profile, cnt in hist.items():
        for kk, v in n_poly(profile).items():
            if v:
                M3[kk] = M3.get(kk, 0) + cnt * v
    M3 = {kk: qk * v for kk, v in M3.items() if v}

    assert sum(M3.values()) == q ** (n + 3 * k)
    for (a, b, c), v in M3.items():
        assert M3.get((b, a, c), 0) == v and M3.get((a, c, b), 0) == v

    out = {"q": q, "n": n, "k": k, "domain": domain,
           "profiles": {",".join(map(str, kk)): hist[kk] for kk in sorted(hist)},
           "M3": {f"{a},{b},{c}": M3[(a, b, c)] for (a, b, c) in sorted(M3)}}
    print(json.dumps(out, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
