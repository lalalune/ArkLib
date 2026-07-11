"""Uniformity of the generic-antipodal-set count ACROSS pairings sigma (the gate `hm`).

GenericSuperDiagonalLower's `superDiagonal_le_rEnergy` is GATED on:
    hm : for every fixed-point-free involution sigma of Fin(2r),
         #genericAntipodalSet G sigma = m   (a CONSTANT, same m for all sigma).

genericAntipodalSet G sigma = { c : Fin(2r) -> G | (forall i, c(sigma i) = -c i) AND UniqueNeg c }.

CLAIM (field-general, any negation-closed finite G with no 2-torsion on the used classes):
the count #genericAntipodalSet G sigma is INDEPENDENT of sigma. Mechanism: for any two
fixed-point-free involutions sigma, tau there is a permutation rho of Fin(2r) with
tau = rho . sigma . rho^{-1} (all fpf involutions are conjugate), and precomposition c |-> c . rho
is a BIJECTION genericAntipodalSet G sigma -> genericAntipodalSet G tau (it preserves G-membership,
the antipodal-pairing relation conjugates, and UniqueNeg is permutation-invariant).

This probe verifies #genericAntipodalSet G sigma is the SAME for ALL fpf involutions sigma,
over abstract negation-closed integer-model G (Z_n additive, neg = negation) AND multiplicative
mu_n in C. We do NOT assume distinct-class structure beyond the UniqueNeg filter itself.
"""
import itertools


def fpf_involutions(twoR):
    """All fixed-point-free involutions (pairings) of range(twoR), as perms (tuples)."""
    elems = list(range(twoR))

    def rec(rem):
        if not rem:
            yield {}
            return
        first = rem[0]
        for j in range(1, len(rem)):
            partner = rem[j]
            rest = rem[1:j] + rem[j + 1:]
            for sub in rec(rest):
                d = dict(sub)
                d[first] = partner
                d[partner] = first
                yield d
    return list(rec(elems))


def count_generic(G, neg, twoR, sigma):
    """#{ c in G^{2r} : forall i c[sigma[i]] = neg(c[i]) AND UniqueNeg c }."""
    cnt = 0
    for c in itertools.product(G, repeat=twoR):
        # antipodal-paired by sigma
        if not all(c[sigma[i]] == neg[c[i]] for i in range(twoR)):
            continue
        # UniqueNeg: for every i, neg(c[i]) attained at a UNIQUE index
        ok = True
        for i in range(twoR):
            target = neg[c[i]]
            hits = sum(1 for j in range(twoR) if c[j] == target)
            if hits != 1:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


def run_additive_Zn(n, r):
    G = list(range(n))
    neg = {g: (-g) % n for g in G}
    twoR = 2 * r
    sigmas = fpf_involutions(twoR)
    counts = [count_generic(G, neg, twoR, s) for s in sigmas]
    uniform = len(set(counts)) == 1
    h = n // 2
    # expected generic count (n/2)_r * 2^r
    expect = 1
    for i in range(r):
        expect *= (h - i)
    expect *= (2 ** r)
    print("Z_%d r=%d: #fpf-inv=%d counts=%s uniform=%s value=%d expect(n/2)_r*2^r=%d match=%s"
          % (n, r, len(sigmas), sorted(set(counts)), uniform,
             counts[0] if counts else -1, expect,
             (counts and counts[0] == expect)))


def run_mult_mu_n(n, r):
    # mu_n = n-th roots of unity, model as exponents in Z_n with neg(g)=g+n/2 (mult by -1)
    G = list(range(n))
    h = n // 2
    neg = {g: (g + h) % n for g in G}
    twoR = 2 * r
    sigmas = fpf_involutions(twoR)
    counts = [count_generic(G, neg, twoR, s) for s in sigmas]
    uniform = len(set(counts)) == 1
    expect = 1
    for i in range(r):
        expect *= (h - i)
    expect *= (2 ** r)
    print("mu_%d r=%d: #fpf-inv=%d counts=%s uniform=%s value=%d expect=%d match=%s"
          % (n, r, len(sigmas), sorted(set(counts)), uniform,
             counts[0] if counts else -1, expect,
             (counts and counts[0] == expect)))


def main():
    print("=== additive Z_n (neg = additive negation; has 2-torsion at n/2) ===")
    for (n, r) in [(4, 1), (4, 2), (6, 1), (6, 2), (8, 1), (8, 2), (8, 3)]:
        run_additive_Zn(n, r)
    print("=== multiplicative mu_n (neg = *(-1) = +n/2) ===")
    for (n, r) in [(4, 1), (4, 2), (8, 1), (8, 2), (8, 3)]:
        run_mult_mu_n(n, r)


if __name__ == "__main__":
    main()
