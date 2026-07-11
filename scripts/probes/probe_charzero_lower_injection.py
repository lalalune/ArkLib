"""Verify the explicit injection that proves  E_r(mu_n) >= (2r-1)!! * (n/2)_r * 2^r.

Construction of a zero-sum 2r-tuple from a triple (matching, signs, class-choice):
  - choose a perfect matching sigma of Fin(2r)  [ (2r-1)!! ways ]
  - choose r DISTINCT antipodal classes via injective phi : Fin r -> {pairs}  [ (n/2)_r ways ]
  - choose r signs eps in {+1,-1}^r                                            [ 2^r ways ]
  Build tuple c: for each matched pair {i, sigma i} (i < sigma i), assign the
  pair the class phi(rank) with sign eps(rank): c_i = eps * g, c_{sigma i} = -eps * g,
  where g is the chosen antipodal-class representative. Then within each pair the two
  entries are antipodal => sum over pair = 0 => total sum = 0.  GOAL: this map
  (matching, classes, signs) -> tuple is INJECTIVE when classes are DISTINCT.

We test injectivity exhaustively for small (n, r) and confirm the image size = A_r,
and that A_r <= true zeroSumCount (already shown).  Injectivity <=> distinct triples
give distinct tuples.
"""
import itertools


def pairings(twoR):
    # all perfect matchings of range(twoR) as frozenset of frozenset pairs
    elems = list(range(twoR))
    def rec(rem):
        if not rem:
            yield ()
            return
        first = rem[0]
        for j in range(1, len(rem)):
            pair = (first, rem[j])
            rest = rem[1:j] + rem[j+1:]
            for sub in rec(rest):
                yield (pair,) + sub
    return list(rec(elems))


def descfact(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


def doublefact(m):
    r = 1
    while m > 0:
        r *= m
        m -= 2
    return r


def main():
    for k in [2, 3]:
        n = 2 ** k
        half = n // 2
        # antipodal classes: exponent j in 0..half-1 represents the pair {zeta^j, zeta^{j+half}=-zeta^j}
        classreps = list(range(half))
        for r in [1, 2]:
            twoR = 2 * r
            if r > half:
                continue
            matchings = pairings(twoR)
            images = set()
            count_triples = 0
            for sigma in matchings:
                # injective class choice: ordered r-tuples of distinct classes
                for phi in itertools.permutations(classreps, r):
                    for eps in itertools.product([1, -1], repeat=r):
                        count_triples += 1
                        # build tuple of exponents-with-sign; represent value as (exp, sign)
                        c = [None] * twoR
                        for rank, (i, j) in enumerate(sigma):
                            g = phi[rank]   # class exponent
                            s = eps[rank]
                            # c_i = s * zeta^g ; c_j = -s * zeta^g = s * zeta^{g+half}
                            c[i] = (g, s)
                            c[j] = ((g + half) % n, s) if False else (g, -s)
                        images.add(tuple(c))
            A_r = doublefact(2 * r - 1) * descfact(half, r) * (2 ** r)
            print("n=%d r=%d: triples=%d  distinct_images=%d  A_r=%d  injective? %s  triples==A_r? %s"
                  % (n, r, count_triples, len(images), A_r,
                     len(images) == count_triples, count_triples == A_r))


if __name__ == "__main__":
    main()
