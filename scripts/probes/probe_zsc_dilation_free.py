"""Confirm n | zeroSumCount(mu_n, r) via FREE multiplicative dilation, incl big primes p>n^3
and Fermat 257 (#444 signed lane). Stronger than the global-negation 2 | zsc.

mu_n = order-n subgroup of F_p^* (so multiplicatively closed, 0 not in it). The dilation
action g.(t_1..t_r) = (g t_1 .. g t_r) for g in mu_n: preserves sum=0 (g*sum=0) and maps
mu_n-tuples to mu_n-tuples. FREE on zero-sum tuples of length r>=1: g.t = t with some t_i != 0
(true since 0 not in mu_n, every coord nonzero) => g = t_i/t_i = 1. Free action of a group of
order n => every orbit has size n => n | zeroSumCount.

Probe: (A) n | zsc for r in 1..5, primes incl p>n^3 + Fermat 257. (B) verify freeness directly:
for every zero-sum tuple and every g != 1 in mu_n, g.t != t.
"""
import itertools


def primes_one_mod_n(n, min_ratio=2, count=3, want_big=False):
    res = []
    k = 1
    while len(res) < count:
        p = k * n + 1
        k += 1
        if p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)) and (p - 1) // n >= min_ratio:
            if (not want_big) or p > n ** 3:
                res.append(p)
        if k > n ** 3 + 8000:
            break
    return res


def mun(n, p):
    for a in range(2, p):
        x = a % p
        kk = 1
        while x != 1 and kk <= p:
            x = (x * a) % p
            kk += 1
        if kk == n:
            S = []
            x = 1
            for _ in range(n):
                S.append(x)
                x = (x * a) % p
            return sorted(set(S))
    return None


def main():
    print("PART A: n | zeroSumCount(mu_n, r)")
    print(f"{'n':>3} {'p':>7} {'big?':>5} | r1 r2 r3 r4 r5  (Y=n divides zsc)")
    configs = []
    for n in [4, 8]:
        for p in primes_one_mod_n(n, count=2) + primes_one_mod_n(n, count=2, want_big=True):
            configs.append((n, p, p > n ** 3))
    if all(not (n == 8 and p == 257) for (n, p, _) in configs):
        configs.append((8, 257, 257 > 8 ** 3))
    for (n, p, big) in configs:
        S = mun(n, p)
        if S is None or len(S) != n:
            continue
        row = []
        for r in [1, 2, 3, 4, 5]:
            if n ** r > 4_000_000:
                row.append(".")
                continue
            z = sum(1 for t in itertools.product(S, repeat=r) if sum(t) % p == 0)
            row.append("Y" if z % n == 0 else "N")
        print(f"{n:>3} {p:>7} {str(big):>5} | " + "  ".join(row))

    print()
    print("PART B: freeness check (n=8 p=17, r=3): for every zero-sum t and g!=1 in mu_n, g.t != t")
    n, p = 8, 17
    S = mun(n, p)
    bad = 0
    for t in itertools.product(S, repeat=3):
        if sum(t) % p != 0:
            continue
        for g in S:
            if g == 1:
                continue
            gt = tuple((g * x) % p for x in t)
            if gt == t:
                bad += 1
    print(f"  fixed-point violations (g!=1 fixing a zero-sum tuple): {bad}  (expect 0 => FREE)")


if __name__ == "__main__":
    main()
