#!/usr/bin/env python3
"""
PROBE (reverse partition direction, #444 census face): the alignableSets (the CensusDomination
object that must be capped by K) is UPPER-bounded by the distinct-gamma count times the per-scalar
max multiplicity:

    #alignableSets <= #pinnedScalars * maxMult,    maxMult := max_gamma #alignedSetsForScalar(gamma).

This is the structural DUAL of the in-tree pinnedScalars_card_mul_le_alignable
(#pinned * minMult <= #alignable).  Engine: #alignableSets = sum_{pinned gamma} mult(gamma) and each
mult(gamma) <= maxMult, so the sum is <= #pinned * maxMult.  Capping a per-scalar multiplicity then
caps the alignableSets count (the CensusDomination obligation) via the distinct-gamma count.

We ALSO measure maxMult against the per-explainer binomial C(|A_gamma|, a) (AgreementSetMaximal:
the a-subsets explained by one codeword number C(|A_gamma|, a)) to see how the multi-explainer
multiplicity relates to the single-explainer count.

Structured planted-codeword words on PROPER thin mu_n (n=2^a), prize-regime p (p >> n^3, p == 1 mod n).
NEVER n = q-1.
"""
import itertools, random
from math import comb
from sympy import isprime, primitive_root

def find_p(n, beta=4):
    p = n**beta + 1
    while True:
        if (p - 1) % n == 0 and isprime(p):
            return p
        p += 1

def mu_n(p, n):
    g = primitive_root(p); h = pow(g, (p - 1) // n, p)
    return sorted({pow(h, i, p) for i in range(n)})

def lowdeg(dom, k, p, c):
    return [sum(c[e] * pow(x, e, p) for e in range(k)) % p for x in dom]

def residual_val(u, tup, dom, k, p):
    xs = [dom[i] for i in tup]; ys = [u[i] for i in tup]
    M = [[pow(xs[j], e, p) for e in range(k)] + [ys[j]] for j in range(k)]; m = k
    for col in range(m):
        piv = None
        for r in range(col, m):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return 1
        M[col], M[piv] = M[piv], M[col]; inv = pow(M[col][col], p - 2, p)
        M[col] = [(v * inv) % p for v in M[col]]
        for r in range(m):
            if r != col and M[r][col] % p != 0:
                f = M[r][col]; M[r] = [(M[r][i] - f * M[col][i]) % p for i in range(m + 1)]
    coeffs = [M[i][m] % p for i in range(m)]
    return (sum(coeffs[e] * pow(xs[k], e, p) for e in range(k)) - ys[k]) % p

def analyze(n, k, a, beta, seed, s):
    p = find_p(n, beta); dom = mu_n(p, n); random.seed(seed)
    s = min(s, n)
    T = sorted(random.sample(range(n), s))
    cA = [random.randrange(p) for _ in range(k)]; cB = [random.randrange(p) for _ in range(k)]
    fA = lowdeg(dom, k, p, cA); fB = lowdeg(dom, k, p, cB)
    u0 = [random.randrange(p) for _ in range(n)]; u1 = [random.randrange(p) for _ in range(n)]
    for i in T:
        u0[i] = fA[i]; u1[i] = fB[i]
    mult = {}     # gamma -> count of aligned a-sets
    nal = 0
    for S in itertools.combinations(range(n), a):
        ts = list(itertools.combinations(S, k + 1)); cand = None; nd = False
        for t in ts:
            r0 = residual_val(u0, t, dom, k, p); r1 = residual_val(u1, t, dom, k, p)
            if not (r0 == 0 and r1 == 0):
                nd = True
                cand = (-r0 * pow(r1, p - 2, p)) % p if r1 % p != 0 else None
                break
        if not nd or cand is None:
            continue
        if all((residual_val(u0, t, dom, k, p) + cand * residual_val(u1, t, dom, k, p)) % p == 0 for t in ts):
            nal += 1; mult[cand] = mult.get(cand, 0) + 1
    if not mult:
        return p, 0, 0, 0, 0
    npn = len(mult); maxm = max(mult.values())
    return p, npn, nal, maxm, comb(s, a) if s >= a else 0

print("n  k a  s  p       #pinned #align maxMult C(s,a)  #align<=#pinned*maxMult?  maxMult<=C(s,a)?")
for (n, k, a, beta, s) in [(8,2,4,4,5),(8,2,4,4,6),(8,2,5,4,6),(8,2,5,4,7),
                           (16,2,5,4,8),(16,2,6,4,10),(16,2,6,4,12),(16,2,7,4,12)]:
    for seed in [1, 2, 3]:
        p, npn, nal, maxm, csa = analyze(n, k, a, beta, seed, s)
        if npn == 0:
            print(f"{n:2} {k} {a} {s:2} {p:7}  (no pinned)"); continue
        revbound = npn * maxm
        ok = "YES" if nal <= revbound else "NO!!"
        capok = "YES" if maxm <= csa else "no"
        print(f"{n:2} {k} {a} {s:2} {p:7}  {npn:4}   {nal:4}   {maxm:4}  {csa:5}    {ok} (#pinned*maxMult={revbound})        {capok}")
