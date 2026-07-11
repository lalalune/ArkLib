#!/usr/bin/env python3
"""
probe_period_subgaussian.py  (#389 ceiling-constant lane, Fable 2026-06-13)

A POSITIVE result, not a refutation: the char-0 (typical-q) 2-power Gaussian
periods of mu_n subset F_q are STRICTLY SUB-GAUSSIAN with variance n, hence the
worst period satisfies  max|eta| <= sqrt(2 n log((q-1)/n)) (1+o(1)).

This makes rigorous the earlier "periods are random-like ~ sqrt(n log q)"
heuristic. The proof chain (verified numerically below):

  (a) closed-walk identity (K1): the char-0 period moment
        E_r = #{2r-step closed walks on Z^{n/2}} = E[T_d^{2r}],
      T_d = sum_{j=1}^{n/2} 2 cos(theta_j)   (d = n/2)
      [constant term of (sum_j (z_j + z_j^{-1}))^{2r}, z_j on the unit circle].

  (b) 2cos(theta) is STRICTLY sub-Gaussian: its MGF is the Bessel function
        E[e^{lam 2cos}] = I_0(2 lam) = sum_k lam^{2k}/(k!)^2
                       <= sum_k lam^{2k}/k! = e^{lam^2}
      term-by-term, since (k!)^2 >= k!  <=>  k! >= 1  (always).
      So its sub-Gaussian proxy equals its variance = 2 (not Hoeffding's loose 4).

  (c) sum of n/2 independent strict-sub-Gaussian(proxy 2) variables is
      sub-Gaussian with proxy 2*(n/2) = n, hence
        E_r = E[T_d^{2r}] <= (2r-1)!! * n^r       (Gaussian-variance-n moment).

  (d) union bound over the f = (q-1)/n periods:
        max|eta| <= sqrt(2 n log f) (1+o(1)).

Honest scope: the bound holds in the char-0 regime where the F_q period moment
equals the walk count, i.e. q >> n^{2r}. The inflation onset r* (smallest r with
E_r(F_q) > walk) tracks log_n q. The delta-star-binding deep band needs moment
order r ~ band depth ~ n/log n, which exceeds r* at production q -> that band is
in the INFLATED regime where this bound does NOT apply (= the open BGK core).
So this controls SHALLOW bands (m < log_n q) rigorously; deep bands stay open.
"""
import math
import cmath


def first_root_of_unity(p, n):
    """A primitive n-th root of unity mod p (n | p-1)."""
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        if all(pow(h, d, p) != 1 for d in range(1, n)):
            return [pow(h, i, p) for i in range(n)]
    raise ValueError("no root found")


def primitive_root(p):
    import sympy
    for cand in range(2, p):
        if all(pow(cand, (p - 1) // pf, p) != 1 for pf in sympy.primefactors(p - 1)):
            return cand
    raise ValueError


def periods(p, n):
    """The (q-1)/n Gaussian periods of the index-(q-1)/n subgroup mu_n (real, since mu_n = -mu_n)."""
    g = primitive_root(p)
    mu = set(first_root_of_unity(p, n))
    f = (p - 1) // n
    seen, etas, gj = set(), [], 1
    for _ in range(f):
        coset = frozenset((gj * a) % p for a in mu)
        if coset not in seen:
            seen.add(coset)
            etas.append(sum(cmath.exp(2j * cmath.pi * a / p) for a in coset).real)
        gj = (gj * g) % p
    return etas


def walk_count(n, r):
    """E[T_d^{2r}], T_d = sum_{j=1}^{d} 2cos(theta_j), d = n/2 = char-0 period moment."""
    d = n // 2
    from collections import Counter

    def parts(rem, maxpart):
        if rem == 0:
            yield []
            return
        for q in range(min(rem, maxpart), 0, -1):
            for rest in parts(rem - q, q):
                yield [q] + rest

    total = 0
    for P in parts(r, r):
        if len(P) > d:
            continue
        c = Counter(P)
        ways = math.factorial(d) // math.factorial(d - len(P))
        for v in c.values():
            ways //= math.factorial(v)
        term = math.factorial(2 * r)
        for p_ in P:
            term //= math.factorial(p_) ** 2
        total += ways * term
    return total


def double_factorial(r):
    """(2r-1)!!"""
    x = 1
    for i in range(1, 2 * r, 2):
        x *= i
    return x


def main():
    print("=" * 72)
    print("(b) Bessel inequality  I_0(2L) <= e^{L^2}  [2cos is strictly sub-Gaussian]")
    print("=" * 72)
    try:
        import mpmath as mp
        for L in [0.3, 0.7, 1.0, 1.5, 2.0, 3.0]:
            i0, eg = mp.besseli(0, 2 * L), mp.e ** (L * L)
            print(f"  L={L}: I_0(2L)={float(i0):.4f}  e^(L^2)={float(eg):.4f}  holds={i0 <= eg}")
    except ImportError:
        print("  (mpmath not available; inequality is term-by-term 1/(k!)^2 <= 1/k!)")

    print("=" * 72)
    print("(c) walk-count moment  E_r <= (2r-1)!! * n^r  [sub-Gaussian, variance n]")
    print("=" * 72)
    for n in [8, 16]:
        for r in range(1, 6):
            w, g = walk_count(n, r), double_factorial(r) * n ** r
            print(f"  n={n} r={r}: E_r={w}  Gaussian={g}  E_r<=G? {w <= g}  ratio={w / g:.3f}")

    print("=" * 72)
    print("(d) period stats: variance ~ n, kurtosis ~ 3, max <= sqrt(2n log f)")
    print("=" * 72)
    for (n, q) in [(8, 257), (8, 1009), (16, 257), (16, 1153),
                   (32, 257), (32, 929), (16, 3217), (8, 2017)]:
        if (q - 1) % n:
            continue
        e = periods(q, n)
        f = len(e)
        m2 = sum(x * x for x in e) / f
        m4 = sum(x ** 4 for x in e) / f
        mx = max(abs(x) for x in e)
        ev = math.sqrt(2 * m2 * math.log(f)) if f > 1 else 0.0
        print(f"  n={n} q={q} f={f}: var={m2:.2f}(~n) kurt={m4 / m2 ** 2:.2f}(G=3) "
              f"max={mx:.2f}  sqrt(2var log f)={ev:.2f}  ratio={mx / ev:.2f}")


if __name__ == "__main__":
    main()
