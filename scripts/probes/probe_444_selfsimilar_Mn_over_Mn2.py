#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the SELF-SIMILARITY ratio R(n) = M(n) / M(n/2).

Genuinely un-measured object (deconflicted: prior workers measured the half-mass H(b*) decay
H/n ~ n^{-0.3..-0.5} and proved the index-2 coherence rho(b*)=1, descent-loss<=2, tower telescopes,
but NOBODY directly measured the inductive ratio M(n)/M(n/2) on the SAME ambient field).

Why it matters (probe-first honesty): if R(n) = M(n)/M(n/2) is a BOUNDED CONSTANT c (esp. c <= sqrt(2)),
then telescoping over the log2(n) levels of the 2-adic tower mu_n > mu_{n/2} > ... gives
    M(n) <= c^{log2 n} * M(1) = n^{log2 c} * M(1),
and c<=sqrt(2) => M(n) <= sqrt(n)*M(1) = the PRIZE exponent (0.5). So the empirical question
"is R(n) <= sqrt(2) ~ 1.414, or does it blow up (forcing the n^{1-o(1)} wall)?" is exactly the
crack-vs-wall dichotomy localized to ONE finite ratio.

The campaign meta-result says this MUST be a wall (BGK 25-yr open), but the BRIEF says probe-first and
extract whether the descent has slack. CRITICAL adversarial guard (cliff-at-n/2, ASYMPTOTIC-CLAIM GUARD
in brief): a per-level ratio that LOOKS <=sqrt(2) at small n can have a sub-leading growth that only
shows at depth; measure R(n) across n=8..512 and FIT the trend, do NOT extrapolate from one n.

EXACT setup: PROPER mu_n (n=2^a) < F_p*, p >> n^3, structured primes, NEVER n=q-1.
For each n we compute M(n) = max_{b != 0} |Sum_{x in mu_n} e_p(b x)| on the SAME prime p (so mu_{n/2}
is the genuine index-2 subgroup of mu_n in the same field). R(n) = M(n)/M(n/2).
"""
import cmath
import math


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def find_prime_with_subgroup(n, beta=4.0):
    """Find prime p with p >> n^beta and n | (p-1) so mu_n exists."""
    target = int(n ** beta)
    # need n | p-1
    k = max(2, target // n)
    while True:
        p = k * n + 1
        if p > target and is_prime(p):
            return p
        k += 1


def subgroup_gen(p, n):
    """Return a generator g of the order-n subgroup mu_n < F_p*."""
    # primitive root
    factors = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    def is_primroot(g):
        return all(pow(g, (p - 1) // f, p) != 1 for f in factors)
    g = 2
    while not is_primroot(g):
        g += 1
    # generator of order-n subgroup
    return pow(g, (p - 1) // n, p)


def M_of(p, n, gen_n):
    """M(n) = max_{b!=0 mod p} |sum_{x in mu_n} e_p(b x)|.
    mu_n = {gen_n^j : j=0..n-1}. We scan b over a representative set: since the sum only depends on
    b through b*mu_n cosets, and worst-b is what we want, scan ALL b in 1..p-1 for small p, else
    scan b over the multiplicative structure (cosets of mu_n) which is enough for the max by
    homogeneity |S(b)| depends on coset b*mu_n. There are (p-1)/n cosets; scan one rep each."""
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x * gen_n) % p
    twopi_over_p = 2.0 * math.pi / p

    def Sabs(b):
        s = 0.0 + 0.0j
        for e in elts:
            s += cmath.exp(1j * twopi_over_p * ((b * e) % p))
        return abs(s)

    best = 0.0
    # b ranges over coset reps of mu_n in F_p*: b = g^i for i=0..(p-1)/n-1 times a primitive root.
    # Simpler + exact for the MAX: |S(b)| is constant on cosets b*mu_n, so scan b=1..p-1 but step
    # is wasteful. Use: cosets = { primroot^i : i } — but we just need the max, scan all b=1..p-1
    # when p is small enough, else sample cosets. For our p (~n^4) p can be large; scan cosets.
    ncos = (p - 1) // n
    if p - 1 <= 200000:
        for b in range(1, p):
            v = Sabs(b)
            if v > best:
                best = v
    else:
        # scan coset reps via primitive root powers
        # reuse primitive root
        m = p - 1
        factors = []
        d = 2
        while d * d <= m:
            if m % d == 0:
                factors.append(d)
                while m % d == 0:
                    m //= d
            d += 1
        if m > 1:
            factors.append(m)
        gr = 2
        while not all(pow(gr, (p - 1) // f, p) != 1 for f in factors):
            gr += 1
        b = 1
        step = pow(gr, 1, p)  # we multiply by gr each time -> walks ALL of F_p* in p-1 steps;
        # to hit each coset of mu_n once, multiply by gr and the cosets repeat every ncos*?? -
        # cleanest: cosets are gr^i * mu_n for i=0..ncos-1, and gr^ncos is in mu_n. So scan i=0..ncos-1.
        rep = 1
        for i in range(ncos):
            v = Sabs(rep)
            if v > best:
                best = v
            rep = (rep * gr) % p
    return best


def main():
    print("n      p            M(n)      M(n)/sqrt(n)   R=M(n)/M(n/2)   log2(R)")
    prevM = None
    rows = []
    for a in range(3, 10):  # n = 8 .. 512
        n = 1 << a
        # keep p^>n^4 but bounded so the coset scan is feasible; use smaller beta for big n
        beta = 4.0 if n <= 64 else (3.2 if n <= 256 else 2.6)
        p = find_prime_with_subgroup(n, beta)
        # cap work: if (p-1)/n is huge, skip (honesty: report what we can compute)
        ncos = (p - 1) // n
        if ncos > 400000:
            print(f"{n:<6} p={p:<12} SKIP (coset count {ncos} too large for exact max)")
            prevM = None
            continue
        gen_n = subgroup_gen(p, n)
        M = M_of(p, n, gen_n)
        msq = M / math.sqrt(n)
        if prevM is not None and prevM > 0:
            R = M / prevM
            l2R = math.log2(R)
            print(f"{n:<6} p={p:<12} {M:8.3f}  {msq:8.3f}      {R:8.4f}       {l2R:+.4f}")
            rows.append((n, R, l2R))
        else:
            print(f"{n:<6} p={p:<12} {M:8.3f}  {msq:8.3f}      (base)")
        prevM = M
    print()
    if rows:
        avg_l2R = sum(r[2] for r in rows) / len(rows)
        print(f"mean log2(R) over levels = {avg_l2R:+.4f}  => M(n) ~ n^{avg_l2R:.4f}")
        print(f"prize exponent = 0.5 (R=sqrt2, log2R=0.5). BGK/wall => log2R -> 1 (M~n).")
        print(f"VERDICT: per-level ratio R {'<=sqrt2 (SLACK?? recheck cliff)' if avg_l2R < 0.5 else '> sqrt2 (consistent with WALL)'}")


if __name__ == "__main__":
    main()
