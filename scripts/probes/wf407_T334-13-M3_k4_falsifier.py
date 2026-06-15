#!/usr/bin/env python3
"""WF407 / T334-13-M3 : the k=4 / M4 census FALSIFIER.

Thread T334-13-M3 (issue #407, ex #334-T13).  Context (proven in-tree):
  * M1, M2 of the agreement spectrum are DOMAIN-INDEPENDENT (enter only through the
    MDS weight enumerator).   [AgreementMomentTwo.lean, O120/O122]
  * M3 (third moment) IS DOMAIN-DEPENDENT - the FIRST separator.  What it measures
    is the pencil census t2 (Mobius-involution 2-orbit counts); smooth subgroups
    spike on the torus-normalizer family {x->c/x}u{x->-x}.   [O133, RESULTS-M3.md]

THE FALSIFIER (this probe).  M_r decomposes over (r-1)-tuples of codewords:
    M2 ~ 1 codeword (weight enumerator)         -> domain-independent
    M3 ~ 2 codewords (2-dim subcode = pencil)   -> domain-DEPENDENT  (level 1)
    M4 ~ 3 codewords (3-dim subcode = cross-ratio/curve census)
Question: does the smooth-vs-random separation SURVIVE at M4 (and at M3 with larger
code dim k), or does the census RE-CONVERGE (smooth indistinguishable again)?
  * re-converges  => census controls only the lowest separating level, M3 direction DIES.
  * still separates => the separation LIVES at every higher moment; weaponizable.

We also track the SIGNAL STRENGTH  rel = |Delta M_r| / M_r  at the argmax cell, the
quantity that an upper-bound (Chebyshev) argument must exploit.  Everything below is
EXACT integer arithmetic over F_q (no sampling on the structured side; random domains
are exact instances, several seeds).

Reproduce:  python wf407_T334-13-M3_k4_falsifier.py
"""

import itertools
import math
import random
import sys
from operator import eq


def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    f = 3
    while f * f <= m:
        if m % f == 0:
            return False
        f += 2
    return True


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q):
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e)
        e = (e * h) % q
    assert len(set(out)) == n
    return sorted(out)


def codewords(q, k, domain):
    n = len(domain)
    pows = [[pow(x, e, q) for e in range(k)] for x in domain]
    return [
        tuple(sum(c[e] * pows[i][e] for e in range(k)) % q for i in range(n))
        for c in itertools.product(range(q), repeat=k)
    ]


def moment_tensors(q, k, domain, rmax):
    """Return dict r -> {tuple(j_1..j_r): count} for r=1..rmax, exact, over all q^n words.

    M_r[j_1,...,j_r] = sum_u prod_i a_{j_i}(u).  Since M_r is S_r-symmetric and its
    domain-separating content lives on the diagonal-clustered cells (argmax always
    (k-1,...,k-1)), we accumulate the full SYMMETRIC tensor as a multiset histogram:
    for each word u with agreement histogram a = (a_0,...,a_n), and each unordered
    r-multiset of indices we add prod a_{j_i}.  We key by the sorted tuple to halve
    storage; the diagonal cell (j,...,j) gets a_j^r."""
    n = len(domain)
    qk = q ** k
    cws = codewords(q, k, domain)
    assert len(cws) == qk
    M = {r: {} for r in range(1, rmax + 1)}
    for u in itertools.product(range(q), repeat=n):
        hist = [0] * (n + 1)
        for cw in cws:
            hist[sum(map(eq, cw, u))] += 1
        assert sum(hist) == qk
        support = [(j, aj) for j, aj in enumerate(hist) if aj]
        for r in range(1, rmax + 1):
            Mr = M[r]
            # unordered multisets of size r from support (sorted-tuple keyed)
            for combo in itertools.combinations_with_replacement(support, r):
                key = tuple(c[0] for c in combo)
                prod = 1
                for c in combo:
                    prod *= c[1]
                Mr[key] = Mr.get(key, 0) + prod
    return M


def tensor_diff(a, b):
    keys = set(a) | set(b)
    worst, arg, pair, ndiff = 0, None, None, 0
    for kk in keys:
        va, vb = a.get(kk, 0), b.get(kk, 0)
        d = abs(va - vb)
        if d:
            ndiff += 1
            if d > worst:
                worst, arg, pair = d, kk, (va, vb)
    return ndiff, worst, arg, pair


def run_cell(q, k, n, rmax, nseed=4):
    print(f"\n===== q={q}, n={n}, k={k}, moments up to M{rmax} "
          f"(brute over {q**n} words x {q**k} codewords) =====")
    H = subgroup(q, n)
    Msub = moment_tensors(q, k, H, rmax)
    # closed-form M1 check (domain-independent sanity)
    for j in range(n + 1):
        exp = (q ** k) * math.comb(n, j) * (q - 1) ** (n - j)
        assert Msub[1][(j,)] == exp, "M1 closed form broken"
    rand = []
    for seed in range(1, nseed + 1):
        dom = sorted(random.Random(1000 * q + seed).sample(range(1, q), n))
        rand.append((seed, dom, moment_tensors(q, k, dom, rmax)))
    # also a coset (must be IDENTICAL to subgroup at every moment by affine invariance)
    Hset = set(H)
    g = next(x for x in range(2, q) if x not in Hset)
    coset = sorted(x * g % q for x in H)
    Mcos = moment_tensors(q, k, coset, rmax)

    results = {}
    for r in range(2, rmax + 1):
        # subgroup vs each random; record min separation and signal strength
        seps = []
        for seed, dom, Mr in rand:
            nd, w, arg, pair = tensor_diff(Msub[r], Mr[r])
            rel = (w / pair[0]) if (pair and pair[0]) else 0.0
            seps.append((nd, w, arg, pair, rel))
        # random-vs-random null (cloud diameter)
        nullmax = 0
        for i in range(len(rand)):
            for jx in range(i + 1, len(rand)):
                _, w, _, _ = tensor_diff(rand[i][2][r], rand[jx][2][r])
                nullmax = max(nullmax, w)
        # coset must match subgroup exactly
        ndc, _, _, _ = tensor_diff(Msub[r], Mcos[r])
        sub_min_sep = min(s[1] for s in seps)
        sub_any_diff = any(s[0] > 0 for s in seps)
        argmax_rel = max(s[4] for s in seps)
        print(f"  M{r}: subgroup-vs-random min|D|={sub_min_sep}  "
              f"random-cloud diam={nullmax}  separates={'YES' if sub_min_sep > nullmax else 'no'}"
              f"  (any diff at all: {sub_any_diff})")
        print(f"        coset==subgroup exactly: {ndc == 0}   "
              f"max signal rel|D|/M={argmax_rel:.3e}  at argmax cell {seps[0][2]}")
        results[r] = dict(sub_min_sep=sub_min_sep, nullmax=nullmax,
                          separates=sub_min_sep > nullmax,
                          any_diff=sub_any_diff, coset_eq=(ndc == 0),
                          argmax_rel=argmax_rel)
    return results


def main():
    print("WF407 / T334-13-M3 : k=4 / M4 census falsifier (exact integers)")
    grid = [
        # (q, n, k, rmax).  n MUST divide q-1 and be even (so -1 in H).
        # Keep q^n enumerable (< ~3e7).  2-power n preferred (prize-shape).
        (13, 4, 2, 4),   # mu_4 in F_13  : 28561 words   2-power
        (13, 6, 2, 4),   # mu_6 in F_13  : 4.8M words
        (13, 4, 3, 4),   # mu_4, k=3
        (17, 4, 2, 4),   # mu_4 in F_17  : 83521 words   2-power
        (17, 8, 2, 4),   # mu_8 in F_17  : 6.9e9 -- SKIP (handled by note); too big
        (29, 4, 2, 4),   # mu_4 in F_29  : 707281 words  2-power, larger q
        (41, 8, 2, 4),   # mu_8 in F_41  : 7.9e12 -- SKIP; too big
    ]
    # drop cells whose brute cost q^n exceeds the budget
    BUDGET = 8_000_000
    grid = [(q, n, k, r) for (q, n, k, r) in grid if q ** n <= BUDGET]
    print("cells (q^n <= budget):", [(q, n, k) for (q, n, k, _) in grid])
    summary = {}
    for (q, n, k, rmax) in grid:
        summary[(q, n, k)] = run_cell(q, k, n, rmax, nseed=4)

    print("\n\n========== FALSIFIER VERDICT TABLE ==========")
    print(f"{'cell':<16}{'M2 sep':<9}{'M3 sep':<9}{'M4 sep':<9}{'M3 rel':<12}{'M4 rel':<12}")
    for (q, n, k), res in summary.items():
        def fmt(r):
            if r not in res:
                return "-"
            return "SEP" if res[r]["separates"] else ("diff" if res[r]["any_diff"] else "eq")
        m3rel = res.get(3, {}).get("argmax_rel", 0)
        m4rel = res.get(4, {}).get("argmax_rel", 0)
        print(f"q{q}n{n}k{k:<11}{fmt(2):<9}{fmt(3):<9}{fmt(4):<9}{m3rel:<12.2e}{m4rel:<12.2e}")

    # The falsifier reading
    print("\nFALSIFIER READING:")
    lives = any(res.get(4, {}).get("separates") for res in summary.values())
    m4_anydiff = any(res.get(4, {}).get("any_diff") for res in summary.values())
    print(f"  M4 separates (above random cloud) in some cell : {lives}")
    print(f"  M4 shows ANY smooth-vs-random difference        : {m4_anydiff}")
    if lives:
        print("  => census LIVES at M4: smooth domains stay separated at the higher moment.")
    elif m4_anydiff:
        print("  => M4 differs but within random cloud: separation WEAKENS / partial.")
    else:
        print("  => census RE-CONVERGES at M4: M3 was the only separating level; direction DIES.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
