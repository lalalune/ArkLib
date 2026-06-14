#!/usr/bin/env python3
"""Coset agreement-spectrum moments: mean/variance are CLOSED FORM, the open
content is exactly the upper tail (issue #232, post-O115/O118 incidence lane).

For the RS code C = {p : deg p < k} on a domain D (|D| = n) and a received word
u, let A(p,u) = {x in D : p(x) = u(x)} and a_j(u) = #{p : |A(p,u)| = j}.  The
list size at radius w is l(u, w) = sum_{j >= n-w} a_j(u).

CLOSED FORMS (verified exactly here):
  (M1) E_u[a_j] = q^(k-n) * C(n,j) * (q-1)^(n-j)            (first moment)
  (M2) E_u[a_j^2] decomposes over codeword PAIRS by their Hamming distance:
       E_u[a_j^2] = sum_d B_d * P_j(d)  where  B_d = #{(p,p') : dist = d}
       is the (MDS-closed-form) distance distribution and P_j(d) is the
       exact probability that a random u has |A(p)| = |A(p')| = j for a fixed
       pair at distance d:
       P_j(d) = q^(-n) * sum_t C(n-d, t) C(d, j-t)^2 (q-1)^(d-(j-t))
                  * (q-2)^(... ) -- computed here COMBINATORIALLY instead:
       on the d disagreement coordinates u can hit p, p', or neither
       (1,1,q-2 ways); on the n-d agreement coordinates u hits both or
       neither (1, q-1).  So
       P_j(d) = q^(-n) * sum_s C(n-d, s) (q-1)^(n-d-s)
                  * C(d, j-s) * C(d-(j-s), j-s')... -- see code: we count
       (s = common agreements; a = u hits p only; b = u hits p' only;
        need s + a = j, s + b = j  =>  a = b = j - s):
       P_j(d) = q^(-n) * sum_s C(n-d,s) (q-1)^(n-d-s)
                  * C(d, j-s) * C(d-(j-s), j-s) * (q-2)^(d-2(j-s))
       (only s with 0 <= j-s and d - 2(j-s) >= 0; q >= 2 caveat handled).

THE PROBE: at several (q, n, k) with D a smooth multiplicative subgroup,
 (1) verify M1, M2 exactly against full enumeration over all u (small) or
     exact per-u censuses on large samples (big);
 (2) decompose max_u l(u,w) vs mean l(u,w) across the Johnson->capacity band:
     the MAX-TO-MEAN RATIO is the toy derandomization gap -- mean/variance are
     domain-independent (any n-point domain, MDS), so EVERYTHING domain-specific
     about delta* lives in the tail;
 (3) compare the smooth-subgroup domain against random n-point domains over the
     same field: if tails coincide, smoothness costs nothing at toy scale (the
     derandomization conjecture's shadow); record the verdict.

Exit 0 iff all exact checks pass.
"""

import itertools
import random
import sys
from math import comb

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("FAIL:", msg)


def poly_eval(coeffs, x, q):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def mult_subgroup(q, n):
    """The order-n subgroup of GF(q)* (n | q-1), via a generator power."""
    # find a primitive root mod q (q prime here)
    for g in range(2, q):
        seen, x = set(), 1
        ok = True
        for _ in range(q - 1):
            x = x * g % q
            if x in seen:
                ok = False
                break
            seen.add(x)
        if ok and len(seen) == q - 1:
            h = pow(g, (q - 1) // n, q)
            return sorted(pow(h, i, q) for i in range(n))
    raise RuntimeError("no generator")


def mds_distance_distribution(n, k, q):
    """B_d = #{ordered codeword pairs at distance d} = q^k * A_d (MDS weights)."""
    A = [0] * (n + 1)
    A[0] = 1
    dmin = n - k + 1
    for w in range(dmin, n + 1):
        A[w] = comb(n, w) * sum(
            (-1) ** j * comb(w, j) * (q ** (w - dmin + 1 - j) - 1)
            for j in range(w - dmin + 1)
        )
    return [q ** k * A[d] for d in range(n + 1)]


def pair_prob(n, d, j, q):
    """P_j(d): probability over uniform u that both codewords of a fixed pair
    at distance d agree with u on exactly j coordinates."""
    total = 0
    for s in range(0, min(j, n - d) + 1):
        a = j - s  # = u-hits-p-only = u-hits-p'-only on the d disagreement coords
        if d - 2 * a < 0:
            continue
        ways_agree = comb(n - d, s) * (q - 1) ** (n - d - s)
        ways_dis = comb(d, a) * comb(d - a, a) * (q - 2) ** (d - 2 * a)
        if q == 2 and d - 2 * a > 0:
            ways_dis = 0
        total += ways_agree * ways_dis
    return total, q ** n  # numerator, denominator


def census(q, D, k, us):
    """Exact a_j(u) for each u in us, by enumerating the code."""
    n = len(D)
    code = []
    for coeffs in itertools.product(range(q), repeat=k):
        code.append(tuple(poly_eval(coeffs, x, q) for x in D))
    out = []
    for u in us:
        a = [0] * (n + 1)
        for cw in code:
            j = sum(1 for i in range(n) if cw[i] == u[i])
            a[j] += 1
        out.append(a)
    return out


def run_setup(q, n, k, n_random_u, full_u_enum, domain=None, label=""):
    D = domain if domain is not None else mult_subgroup(q, n)
    print(f"\n== q={q} n={n} k={k} {label} D={D if n <= 16 else '...'}")
    rng = random.Random(232)
    if full_u_enum:
        us = [u for u in itertools.product(range(q), repeat=n)]
    else:
        us = [tuple(rng.randrange(q) for _ in range(n)) for _ in range(n_random_u)]
    cens = census(q, D, k, us)
    # (1) exact first moment (only valid as exact equality under full enumeration)
    B = mds_distance_distribution(n, k, q)
    for j in range(n + 1):
        m1_num = q ** k * comb(n, j) * (q - 1) ** (n - j)  # sum over u of a_j
        tot = sum(a[j] for a in cens)
        if full_u_enum:
            if tot != m1_num:
                fail(f"M1 j={j}: census {tot} != closed form {m1_num}")
        # second moment
        m2_num = sum(B[d] * pair_prob(n, d, j, q)[0] for d in range(n + 1))
        tot2 = sum(a[j] ** 2 for a in cens)
        if full_u_enum:
            if tot2 != m2_num:
                fail(f"M2 j={j}: census {tot2} != closed form {m2_num}")
    if full_u_enum:
        print(f"   M1/M2 closed forms: EXACT over all q^{n} received words")
    # (2) max-vs-mean across the band
    import math
    johnson = n - math.sqrt(n * k)
    capacity = n - k
    print(f"   UD={(n-k)//2}  Johnson={johnson:.2f}  capacity={capacity}")
    print(f"   {'w':>3} {'mean l':>12} {'max l':>8} {'ratio':>10}")
    for w in range(max(0, (n - k) // 2), min(n, capacity + 2) + 1):
        thresh = n - w
        means = sum(sum(a[j] for j in range(thresh, n + 1)) for a in cens) / len(us)
        mx = max(sum(a[j] for j in range(thresh, n + 1)) for a in cens)
        ratio = mx / means if means > 0 else float("inf")
        tag = ""
        if abs(w - johnson) < 1:
            tag = "  <-- Johnson"
        if w == capacity:
            tag = "  <-- capacity"
        print(f"   {w:>3} {means:>12.4f} {mx:>8} {ratio:>10.2f}{tag}")
    return cens, us, D


def main():
    rng = random.Random(17)
    # Small: FULL u-enumeration -> exact moment verification (q=5, n=4, k=2:
    # 5^4=625 words x 25 codewords)
    run_setup(5, 4, 2, 0, True, label="(full enum; exact M1/M2 check)")
    # q=7, n=6, k=2: 7^6=117649 x 49 -- still exact
    run_setup(7, 6, 2, 0, True, label="(full enum; exact M1/M2 check)")
    # Medium, sampled: q=17, n=16 smooth subgroup vs random domains
    cens_s, us, _ = run_setup(17, 16, 4, 400, False, label="(smooth subgroup; sampled u)")
    # random 16-point domain in GF(17)*: compare tails on the SAME u sample
    Drand = sorted(rng.sample(range(1, 17), 16))  # n = q-1 = 16: same set!
    # n = q-1 forces same domain; instead use q=257 to get genuinely random domains
    print("\n   [smooth-vs-random needs n < q-1; running q=257 comparison]")
    cens_sm, us2, _ = run_setup(257, 16, 2, 300, False, label="(smooth subgroup of GF(257))")
    rng2 = random.Random(99)
    Dr = sorted(rng2.sample(range(1, 257), 16))
    cens_rd, us3, _ = run_setup(257, 16, 2, 300, False, domain=Dr, label="(random domain in GF(257))")

    print()
    if FAILS:
        print(f"RESULT: {FAILS} FAILURES")
        sys.exit(1)
    print("RESULT: ALL EXACT CHECKS PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
