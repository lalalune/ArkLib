"""Uniqueness of the antipodal pairing sigma on the distinct-class locus.

Claim (the disjointness ENGINE for the char-0 energy lower bound's card_biUnion assembly):
  Let G be negation-closed (g in G => -g in G) with NO 2-torsion (g != -g for g != 0), and let
  c : Fin(2r) -> G be a tuple whose values, grouped into antipodal classes {g,-g}, are such that
  the r antipodal *pairs* it forms all lie in DISTINCT antipodal classes (no class used twice).
  If c is antipodally paired by sigma  (c(sigma i) = -c i, sigma a fixed-point-free involution)
  AND by sigma' (c(sigma' i) = -c i), then sigma = sigma'.

Mechanism: c(sigma i) = -c i means sigma i is THE partner index whose value is -c i. On the
distinct-class locus, for each i there is a UNIQUE index j != i with c j = -c i (the class of c i
is used exactly twice: once as +, once as -). So sigma i is forced = that unique j. Hence sigma is
determined by c, so sigma = sigma'.

We brute-force verify: for random distinct-class antipodally-paired tuples, the sigma that pairs
them is unique; and we check the forcing on ALL pairings.
"""
import itertools


def pairings(twoR):
    elems = list(range(twoR))
    def rec(rem):
        if not rem:
            yield ()
            return
        first = rem[0]
        for j in range(1, len(rem)):
            pair = (first, rem[j])
            rest = rem[1:j] + rem[j + 1:]
            for sub in rec(rest):
                yield (pair,) + sub
    return list(rec(elems))


def perm_from_matching(matching, twoR):
    """matching = tuple of (a,b) pairs -> involution as a function list."""
    f = [None] * twoR
    for (a, b) in matching:
        f[a] = b
        f[b] = a
    return f


def main():
    # model G = Z_n (n even), antipode of g is g + n/2 ; class rep = min(g, g+n/2)
    ok_all = True
    for k in [2, 3]:
        n = 2 ** k
        h = n // 2
        for r in [1, 2, 3]:
            if r > h:
                continue
            twoR = 2 * r
            ms = pairings(twoR)
            # enumerate distinct-class antipodally-paired tuples via (sigma, phi distinct classes, signs)
            checked = 0
            unique_ok = True
            for sigma in ms:
                low = [min(p) for p in sigma]
                for phi in itertools.permutations(range(h), r):
                    for eps in itertools.product([0, 1], repeat=r):
                        c = [None] * twoR
                        for rank, (a, b) in enumerate(sigma):
                            g = (phi[rank] + (h if eps[rank] else 0)) % n
                            lo = min(a, b)
                            hi = max(a, b)
                            c[lo] = g
                            c[hi] = (g + h) % n
                        # now find ALL pairings sigma' that antipodally pair c
                        matches = []
                        for sg2 in ms:
                            f = perm_from_matching(sg2, twoR)
                            if all((c[f[i]] == (c[i] + h) % n) for i in range(twoR)):
                                matches.append(sg2)
                        checked += 1
                        if len(matches) != 1:
                            unique_ok = False
                            ok_all = False
            print("n=%d r=%d: checked %d distinct-class tuples, sigma-unique=%s  #pairings=%d"
                  % (n, r, checked, unique_ok, len(ms)))
    print("ALL UNIQUE:", ok_all)


if __name__ == "__main__":
    main()
