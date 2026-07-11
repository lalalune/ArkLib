"""Probe ODD-order zeroSumCount structure on thin mu_n in F_p (#444 signed lane).

zeroSumCount(S,r) = #{(x_1..x_r) in S^r : sum x_i = 0 in F_p}.
S = mu_n the order-n (thin, n=2^a) subgroup, p == 1 mod n, (p-1)/n >= 2, NEVER n=q-1.

Questions:
 (Q1) Is zeroSumCount(mu_n, r) EVEN for all ODD r? (negation x->-x acts on tuples
      componentwise; for odd r it has NO fixed point on a zero-sum tuple because a
      fixed tuple needs x_i = -x_i i.e. x_i=0 not in S; so the free Z/2 involution
      forces an even count.)  Actually the relevant free involution is GLOBAL negation
      t -> -t (negate every coordinate): sum(-t)= -sum(t)=0 too, and -t != t since
      that needs every x_i=0. So zero-sum set is closed under global negation, free =>
      EVEN cardinality, for ANY r>=1 with 0 not in S.  Test it.
 (Q2) The nonzero signed sum form sum_{psi!=0} eta^r = q*zeroSumCount - n^r. For odd r,
      is this <0 sometimes (genuinely signed, not a sum of squares)? Compare even r
      (should track the energy E_r >= 0 form).
 (Q3) Does zeroSumCount(mu_n, r) for odd r have a clean lower-order term beyond the
      "diagonal pairings" the even-order energy ladder sees?  Print zsc and zsc - (the
      naive main term n^r/p rounded) to see the fluctuation.
"""
import itertools


def primes_one_mod_n(n, min_ratio=2, count=2, want_big=False):
    res = []
    cand = 1
    while len(res) < count and cand < n ** 4 + 5000:
        cand += n  # cand == 1 mod n if we start at 1
        c = cand + 1 if False else cand
        # we want c == 1 mod n: start cand at 1, step n -> cand = 1, 1+n, ...
    # simpler explicit loop:
    res = []
    k = 1
    while len(res) < count:
        p = k * n + 1
        k += 1
        if p <= 2:
            continue
        isp = all(p % d for d in range(2, int(p ** 0.5) + 1))
        if not isp:
            continue
        if (p - 1) // n < min_ratio:
            continue
        if want_big and p <= n ** 3:
            continue
        res.append(p)
        if p > n ** 4 + 5000:
            break
    return res


def mun(n, p):
    for a in range(2, p):
        x = a % p
        k = 1
        while x != 1 and k <= p:
            x = (x * a) % p
            k += 1
        if k == n:
            S = []
            x = 1
            for _ in range(n):
                S.append(x)
                x = (x * a) % p
            return sorted(set(S))
    return None


def zerosumcount(S, p, r):
    cnt = 0
    for t in itertools.product(S, repeat=r):
        if sum(t) % p == 0:
            cnt += 1
    return cnt


def main():
    print(f"{'n':>3} {'p':>7} {'r':>2} {'zsc':>8} {'even?':>6} {'q*W-n^r':>14} {'sign':>5}")
    for n in [4, 8]:
        primes = primes_one_mod_n(n, min_ratio=2, count=3)
        for p in primes[:2]:
            S = mun(n, p)
            if S is None or len(S) != n:
                continue
            assert all((p - x) % p in S for x in S), "mu_n not negation-closed"
            for r in [2, 3, 4, 5]:
                if n ** r > 6_000_000:
                    continue
                z = zerosumcount(S, p, r)
                even = (z % 2 == 0)
                nonzero_form = p * z - n ** r
                sign = '+' if nonzero_form > 0 else ('0' if nonzero_form == 0 else '-')
                print(f"{n:>3} {p:>7} {r:>2} {z:>8} {str(even):>6} {nonzero_form:>14} {sign:>5}")
    print()
    print("Q1 EVEN-for-all-r check: zsc even <=> global negation t->-t is free on zero-sum set (0 not in S).")
    print("Q2 sign of (q*W_r - n^r): for the located thinness object sum_{psi!=0} eta^r.")


if __name__ == "__main__":
    main()
