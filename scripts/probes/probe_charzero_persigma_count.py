"""Per-pairing distinct-class count + uniqueness of sigma on the generic locus.

For a FIXED pairing sigma of Fin(2r), count zero-sum 2r-tuples c with:
  - c antipodally sigma-paired: c(sigma i) = -c(i) for all i, and
  - the r pair-values {c(i) : i in lowerHalf(sigma)} lie in DISTINCT antipodal classes.
Claim: that count = (n/2)_r * 2^r  (choose r distinct classes ordered on the transversal,
times a sign each).  AND: such a generic tuple determines sigma UNIQUELY (antipodal partners
are the unique same-antipodal-class index pairs), so images over distinct sigma are disjoint.
We verify both for small (n, r).
"""
import itertools
import cmath


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


def descfact(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


def antipodal_class(j, n):
    # class of zeta^j is {j, j+n/2 mod n}; canonical rep = min
    h = n // 2
    return min(j % n, (j + h) % n)


def main():
    for k in [2, 3]:
        n = 2 ** k
        h = n // 2
        for r in [1, 2]:
            if r > h:
                continue
            twoR = 2 * r
            ms = pairings(twoR)
            # per-sigma generic count: fix the first matching, count distinct-class signed tuples
            sigma0 = ms[0]
            # build all c with c paired by sigma0, distinct classes
            per_sigma_imgs = {}
            for sidx, sigma in enumerate(ms):
                imgs = set()
                # transversal = lower index of each pair
                low = [min(p) for p in sigma]
                for phi in itertools.permutations(range(h), r):  # distinct classes (ordered)
                    for eps in itertools.product([0, 1], repeat=r):  # sign: 0->+,1->+half(=neg)
                        c = [None] * twoR
                        for rank, (a, b) in enumerate(sigma):
                            g = phi[rank] + (h if eps[rank] else 0)  # exponent
                            c[min(a, b)] = g % n
                            c[max(a, b)] = (g + h) % n  # antipode
                        imgs.add(tuple(c))
                per_sigma_imgs[sidx] = imgs
            per_count = len(per_sigma_imgs[0])
            expect = descfact(h, r) * (2 ** r)
            # disjointness across sigma
            all_pairs_disjoint = True
            keys = list(per_sigma_imgs.keys())
            for i in range(len(keys)):
                for j in range(i + 1, len(keys)):
                    if per_sigma_imgs[keys[i]] & per_sigma_imgs[keys[j]]:
                        all_pairs_disjoint = False
            print("n=%d r=%d: per_sigma_count=%d  expect (n/2)_r*2^r=%d  match=%s  disjoint_across_sigma=%s  #pairings=%d"
                  % (n, r, per_count, expect, per_count == expect, all_pairs_disjoint, len(ms)))


if __name__ == "__main__":
    main()
