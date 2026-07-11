#!/usr/bin/env python3
"""
probe_persigma_exact_count.py  (#407 lower companion)

CLAIM under test (the EXACT per-sigma antipodal-consistent count, dual of the proven
`antipodalConsistent_card_le : #{c | c(sigma i) = -c i} <= n^r`):

  For a FIXED pairing sigma of Fin(2r) (fixed-point-free involution) and a negation-closed
  finite G subset F (here mu_n in char 0), the antipodal-consistent set
      A_sigma = { c : Fin(2r) -> G | for all i, c(sigma i) = -(c i) }
  has cardinality EXACTLY n^r  (the transversal/lower-half values are FREELY choosable in G,
  the upper-half values are forced by c(sigma i) = -(c i) and land back in G by neg-closure).

Probe-first per brief rule 2: PROPER thin subgroup mu_n in char 0 (here: 2n-th roots of unity
restricted to mu_n = n-th roots), NEVER n=q-1. We do it over the abstract additive structure that
matters: negation-closed G inside an additive abelian group. To stay faithful to the Lean object
(G : Finset F, F a field, neg-closed), we model G as a symmetric subset of Z (negation-closed),
which is exactly the combinatorial content (the field is irrelevant to the COUNT; only neg-closure
+ injectivity of negation matter). We also sanity-check on actual mu_n in C.

VERDICT printed per (n, r, sigma-sample): exact count == n^r ?
"""
import itertools, cmath, math, random

def all_pairings(m):
    # m = 2r ; yield all fixed-point-free involutions (perfect matchings) of range(m)
    pts = list(range(m))
    def rec(rem):
        if not rem:
            yield []
            return
        a = rem[0]
        for j in range(1, len(rem)):
            b = rem[j]
            rest = rem[1:j] + rem[j+1:]
            for tail in rec(rest):
                yield [(a, b)] + tail
    for matching in rec(pts):
        # build involution perm
        perm = list(range(m))
        for (a, b) in matching:
            perm[a] = b
            perm[b] = a
        yield perm

def count_antipodal_consistent(perm, G):
    """Brute force: count c : range(m) -> G with c[perm[i]] == -c[i] for all i.
    G is a negation-closed set of ELEMENTS of an additive group; we use a 'neg' map."""
    m = len(perm)
    Glist = list(G)
    # neg map: for symmetric integer set, neg is arithmetic negation
    count = 0
    # only need to enumerate over free choices on lower half (i < perm[i]); but to be HONEST and
    # avoid baking the claim in, brute-force the full assignment for small cases.
    for c in itertools.product(Glist, repeat=m):
        ok = True
        for i in range(m):
            if c[perm[i]] != -c[i]:
                ok = False
                break
        if ok:
            count += 1
    return count

def main():
    random.seed(1)
    print("=== model: G = symmetric integer set (neg-closed), abstract count ===")
    for n in [2, 4, 6]:           # |G| = n, must be neg-closed symmetric set
        # symmetric set of size n in Z: e.g. {+-1,+-2,...} ; if n even use {+-1..+-(n/2)}
        assert n % 2 == 0
        half = n // 2
        G = set(list(range(1, half+1)) + [-x for x in range(1, half+1)])
        assert len(G) == n and all(-x in G for x in G)
        for r in [1, 2, 3]:
            m = 2*r
            target = n**r
            perms = list(all_pairings(m))
            # sample up to 6 pairings to bound brute-force cost (m up to 6, n up to 6 -> 6^6=46656 ok)
            sample = perms if len(perms) <= 6 else random.sample(perms, 6)
            verdicts = []
            for perm in sample:
                cnt = count_antipodal_consistent(perm, G)
                verdicts.append(cnt == target)
            ok = all(verdicts)
            print(f"  n={n} r={r}  m={m}  #pairings={len(perms)} sampled={len(sample)}  "
                  f"n^r={target}  all_exact={ok}  (counts match n^r: {sum(verdicts)}/{len(sample)})")

    print("=== sanity: actual mu_n in C (n-th roots of unity), neg-closed for even n ===")
    for n in [2, 4]:
        roots = [cmath.exp(2j*math.pi*k/n) for k in range(n)]
        # neg-closed iff -1 in mu_n iff n even
        def neg(z): return -z
        # verify neg-closure
        def close(a, b, tol=1e-9): return abs(a-b) < tol
        assert all(any(close(neg(z), w) for w in roots) for z in roots)
        for r in [1, 2]:
            m = 2*r
            perms = list(all_pairings(m))
            perm = perms[0]
            # brute count with complex equality up to tol
            cnt = 0
            for c in itertools.product(roots, repeat=m):
                if all(close(c[perm[i]], neg(c[i])) for i in range(m)):
                    cnt += 1
            print(f"  mu_{n} r={r}  n^r={n**r}  count={cnt}  exact={cnt==n**r}")

if __name__ == "__main__":
    main()
