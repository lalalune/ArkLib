"""
probe_binder_primitivity_flip — does the BINDING direction's primitivity stay
invariant up the dyadic tower, or does it FLIP?

Context (#444, E3/E5 face). The 50-bridge program (deltastar-444 kb) reduces the
whole prize to ONE open input: bounding the plateau width w per tower level
(B29 `hclean`, B30 `plateauWidthBound`). B26/B27 PROVE: plateau-doubling occurs
EXACTLY at IMPRIMITIVE (even-shift, gcd(b-a,n)>1) directions; PRIMITIVE binders
give clean w=1 descent (no plateau). The spec-doc E3 ASSERTS "at the binding s*
the worst direction is PRIMITIVE (d=1, S=n)" -> which, if true up the tower, would
discharge `hclean` (clean shift) and collapse m* to O(log n) = THE PRIZE.

This probe tests that assertion directly on PROPER thin mu_n subgroups, exact char-0,
p >> n^3, p == 1 mod n, at MULTIPLE primes (p-independence, rule 2), NEVER n=q-1.

VERDICT (run): the binder primitivity is NOT tower-invariant. n=8 binder is PRIMITIVE,
n=16 binder is IMPRIMITIVE (gcd(b-a,16)=2) at every tested prime. The spec-doc's claimed
n=16 binder (11,10) is HEAVY (saturated, in-code) at the binding region, NOT a far-line
binder. So the clean-shift hope FAILS exactly at the first tower step where it would matter:
the binder lands in B27's plateau-doubling regime, not B26's clean regime.
"""
import math
from itertools import combinations


def is_prime(x):
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d = x - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def primes_1_mod_n(n, count, start_mult=1):
    """count smallest primes p >= start_mult*n^4 with p == 1 (mod n)."""
    out = []
    p = max(n * n * n * n, start_mult * n * n * n * n)
    p += (1 - p) % n  # smallest >= p with p == 1 mod n
    if p < n * n * n * n:
        p += n
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def primitive_root(p):
    fs = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            fs.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fs.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    return 0


def ddk(vals, nodes, k, p):
    """k-th divided difference of vals over node points nodes (len k+1)."""
    vs = list(vals[:k + 1])
    for j in range(1, k + 1):
        for i in range(k, j - 1, -1):
            inv = pow((nodes[i] - nodes[i - j]) % p, p - 2, p)
            vs[i] = (vs[i] - vs[i - 1]) * inv % p
    return vs[k]


def in_rs(vals, nodes, k, p):
    s = len(nodes)
    if s <= k:
        return True
    for st in range(s - k):
        if ddk(vals[st:st + k + 1], nodes[st:st + k + 1], k, p) != 0:
            return False
    return True


def incidence(a, b, mu, k, p, s):
    """# distinct gamma s.t. x^a + gamma x^b agrees with a deg<k poly on >= s pts of mu.
       Returns ('HEAVY', None) if any witness has both x^a, x^b in the code (saturated)."""
    n = len(mu)
    mua = [pow(v, a, p) for v in mu]
    mub = [pow(v, b, p) for v in mu]
    gammas = set()
    for comb in combinations(range(n), s):
        nodes = [mu[i] for i in comb]
        u0 = [mua[i] for i in comb]
        u1 = [mub[i] for i in comb]
        if in_rs(u1, nodes, k, p):
            if in_rs(u0, nodes, k, p):
                return ('HEAVY', None)
            continue
        a1 = ddk(u1[:k + 1], nodes[:k + 1], k, p)
        a0 = ddk(u0[:k + 1], nodes[:k + 1], k, p)
        if a1 == 0:
            continue
        gm = (-a0) * pow(a1, p - 2, p) % p
        full = [(u0[i] + gm * u1[i]) % p for i in range(s)]
        if in_rs(full, nodes, k, p):
            gammas.add(gm)
    return (len(gammas), None)


def binder(n, k, p):
    """find s* = least s in [k+2, n) with max far-dir incidence <= budget=n; return (s*, argdir, maxI)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    mu = [pow(h, i, p) for i in range(n)]
    budget = n
    for s in range(k + 2, n):
        best = -1
        arg = None
        for b in range(k, s):
            for a in range(k, n):
                if a == b:
                    continue
                inc, _ = incidence(a, b, mu, k, p, s)
                if inc == 'HEAVY':
                    inc = 0  # saturated dir carries no over-det far-line info
                if inc > best:
                    best = inc
                    arg = (a, b)
        if best <= budget:
            return s, arg, best
    return None, None, None


def run():
    print("BINDER PRIMITIVITY up the dyadic tower (exact char-0, p==1 mod n, multiple primes):\n")
    print(f"{'n':>4} {'k':>3} {'p':>10} {'s*':>3} {'binder':>9} {'b-a':>5} {'gcd':>4} {'verdict':>11}")
    results = {}
    for (n, k) in [(8, 2), (16, 4)]:
        for sm in (1, 2, 3):  # three distinct primes for p-independence (rule 2)
            p = primes_1_mod_n(n, 1, start_mult=sm)[0]
            sstar, arg, mx = binder(n, k, p)
            d = (arg[1] - arg[0]) % n
            gg = math.gcd(d, n)
            verdict = "PRIMITIVE" if gg == 1 else "IMPRIMITIVE"
            results.setdefault(n, []).append(verdict)
            print(f"{n:>4} {k:>3} {p:>10} {sstar:>3} {str(arg):>9} {d:>5} {gg:>4} {verdict:>11}")
    print()
    n8 = set(results[8])
    n16 = set(results[16])
    print(f"n=8  binder verdicts across 3 primes: {n8}")
    print(f"n=16 binder verdicts across 3 primes: {n16}")
    flip = (n8 == {"PRIMITIVE"} and n16 == {"IMPRIMITIVE"})
    print()
    print(f"PRIMITIVITY FLIPS up the tower (p-independent): {flip}")
    if flip:
        print("=> The spec-doc E3 'binder is primitive' is FALSE at n=16. The clean-shift "
              "hope (B26 primitive=>no plateau) does NOT apply at the binder: the binder is "
              "IMPRIMITIVE = exactly B27's plateau-doubling regime. m*-growth stays OPEN.")


if __name__ == "__main__":
    run()
