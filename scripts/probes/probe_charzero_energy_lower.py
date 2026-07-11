"""Probe: char-0 energy LOWER bound  E_r(mu_n) >= (2r-1)!! * (n/2)_r * 2^r.

mu_n = 2^k-th roots of unity in CHAR 0 (complex).  E_r(G) = zeroSumCount G (2r)
for negation-closed G (proven bijection rEnergy_eq_zeroSumCount).  We compute the
exact zero-sum count by brute force on small n and compare to:
  A_r := (2r-1)!! * (n/2)(n/2-1)...(n/2-r+1) * 2^r   (antipodal-pairs lower bound)
  Wick := (2r-1)!! * n^r                              (proven char-0 upper bound)
Verifies A_r <= E_r <= Wick on prize-shape mu_n (proper 2-power subgroups, char 0).
"""
import itertools
import cmath


def doublefact(m):
    r = 1
    while m > 0:
        r *= m
        m -= 2
    return r


def descfact(a, r):
    p = 1
    for i in range(r):
        p *= (a - i)
    return p


def Ar(n, r):
    return doublefact(2 * r - 1) * descfact(n // 2, r) * (2 ** r)


def zerosum_count_exact(n, twoR):
    zeta = cmath.exp(2j * cmath.pi / n)
    roots = [zeta ** j for j in range(n)]
    cnt = 0
    for tup in itertools.product(range(n), repeat=twoR):
        s = 0j
        for j in tup:
            s += roots[j]
        if abs(s) < 1e-7:
            cnt += 1
    return cnt


def main():
    for k in [1, 2, 3]:
        n = 2 ** k
        for r in [1, 2, 3]:
            twoR = 2 * r
            if n ** twoR > 5000000:
                print("n=%d r=%d: SKIP (too big: %d)" % (n, r, n ** twoR))
                continue
            E = zerosum_count_exact(n, twoR)
            lower = Ar(n, r)
            upper = doublefact(2 * r - 1) * (n ** r)
            print("n=%d r=%d: E_r=%d  A_r(lower)=%d  Wick(upper)=%d  E>=A_r? %s  E<=Wick? %s"
                  % (n, r, E, lower, upper, E >= lower, E <= upper))


if __name__ == "__main__":
    main()
