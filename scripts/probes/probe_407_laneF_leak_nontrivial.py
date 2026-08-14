# Lane F (#407): is the cross-parity leak A == -g*B NONTRIVIAL, or just sum u = 0 rewritten?
#
# Round 1 found g0 = -A/B = 1 for 100% of defects under EVERY complementary
# splitting A|B of the SAME sum -- because A+B = sum_{u} u = 0 by definition of a
# spurious config, so A = -B trivially (g=1).  That is VACUOUS.
#
# To make the leak NONTRIVIAL we must compare DIFFERENT objects, not two halves of
# the same vanishing sum.  Natural candidates where g!=1 could carry content:
#   (a) the level-1 vs level-3 sums:  S1 = sum u ,  S3 = sum u^3  (both 0 -> trivial).
#   (b) a partial level-1 vs the SAME partial at level 3:  for a subset A of the
#       config, does  (sum_{A} u^3) == -g (sum_{A} u)  for a FIXED g across defects?
#       (this is a genuine cross-parity = cross-power-level relation).
#   (c) "g" = the Galois/Frobenius element: A = embedding of an ideal, B its conjugate.
#   (d) the e2 bad-scalar relation:  e2 = -1/2 sum u^2 vs sum_{half} u.
#
# This probe stresses (b),(d): genuinely different objects, looking for a FIXED g.

from itertools import combinations
from collections import Counter

def prim(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1:
            return g
    raise RuntimeError

def find_spurious(n, p, sizes):
    g = prim(n, p); mu = [pow(g, j, p) for j in range(n)]; half = n // 2
    out = []
    for size in sizes:
        for cfg in combinations(range(n), size):
            cs = set(cfg)
            if any(((j + half) % n) in cs for j in cfg):
                continue
            us = [mu[j] for j in cfg]
            if sum(us) % p == 0 and sum(pow(u, 3, p) for u in us) % p == 0:
                out.append(cfg)
    return g, mu, out

def report(label, g0_list, n, p, denom):
    if not g0_list:
        print(f"  [{label}] no usable defects (all denominators 0)")
        return
    c = Counter(g0_list)
    top, k = c.most_common(1)[0]
    in_mun = sum(1 for x in g0_list if pow(x, n, p) == 1)
    print(f"  [{label}] over {denom} defects, {len(g0_list)} usable: "
          f"#distinct ratio = {len(set(g0_list))}; "
          f"top ratio {top} covers {k}/{len(g0_list)} ({100*k/len(g0_list):.0f}%); "
          f"ratio in mu_n: {in_mun}/{len(g0_list)}")

def run(n, p, sizes):
    g, mu, spur = find_spurious(n, p, sizes)
    half = n // 2
    print(f"\n##### n={n} p={p}: {len(spur)} spurious configs")
    if not spur:
        return

    # (b) partial cross-power: for the *even-index* part A of each config,
    #     ratio = -(sum_A u^3)/(sum_A u). Is it fixed across defects?
    rb = []
    for cfg in spur:
        A = [mu[j] for j in cfg if j % 2 == 0]
        s1 = sum(A) % p
        s3 = sum(pow(u, 3, p) for u in A) % p
        if s1 != 0:
            rb.append(((-s3) * pow(s1, p - 2, p)) % p)
    report("partial cross-power -(sumA u^3)/(sumA u), even-index half", rb, n, p, len(spur))

    # (b') same but low-index half
    rb2 = []
    for cfg in spur:
        A = [mu[j] for j in cfg if j < half]
        s1 = sum(A) % p
        s3 = sum(pow(u, 3, p) for u in A) % p
        if s1 != 0:
            rb2.append(((-s3) * pow(s1, p - 2, p)) % p)
    report("partial cross-power, low-index half", rb2, n, p, len(spur))

    # (d) e2 bad scalar vs sum-of-squares structure: e2 = -1/2 sum u^2.
    #     ratio of e2 to (sum over even-index u^2) -- looking for fixed g.
    rd = []
    inv2 = pow(2, p - 2, p)
    for cfg in spur:
        e2 = (-inv2 * sum(pow(mu[j], 2, p) for j in cfg)) % p
        denomA = sum(pow(mu[j], 2, p) for j in cfg if j % 2 == 0) % p
        if denomA != 0:
            rd.append((e2 * pow(denomA, p - 2, p)) % p)
    report("e2 / (even-index sum u^2)", rd, n, p, len(spur))

    # SANITY (the vacuous one): A=-B for complementary halves -> ratio must be 1.
    rv = []
    for cfg in spur:
        A = sum(mu[j] for j in cfg if j % 2 == 0) % p
        B = sum(mu[j] for j in cfg if j % 2 == 1) % p
        if B != 0:
            rv.append(((-A) * pow(B, p - 2, p)) % p)
    report("SANITY complementary A=-B (expect ratio 1, vacuous)", rv, n, p, len(spur))

if __name__ == "__main__":
    run(16, 17, [4, 6, 8])
    run(32, 97, [4, 6])
    run(64, 2113, [6])
