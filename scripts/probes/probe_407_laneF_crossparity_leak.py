# Lane F (#407, direction #6): the cross-parity leak  A == -g*B (mod q).
#
# CLAIM TO TEST (from the routing map): the ONE structured feature of the
# spurious-config (defect) locus is a cross-parity relation
#       A == -g * B  (mod q)
# holding for 96-100% of defects, where A,B are the two HALVES of a spurious
# config under some splitting and g is some fixed ring element.
#
# A spurious config here is an antipodal-free U subset mu_n with
#       sum_{u in U} u  == 0   and   sum_{u in U} u^3 == 0   (mod p)
# (the m=2 gap relations e1=e3=0 with no +-pairs).  Over C no such U exists
# (Lam-Leung); over F_p they appear at small saturated primes.  The n=64
# spurious configs at p=2113 are the canonical test data.
#
# This probe:
#  (1) exhaustively enumerates ALL spurious antipodal-free configs at n=64,p=2113
#      (and a few other (n,p));
#  (2) for each, tries several natural SPLITTINGS into halves A,B and tests
#      whether A == -g*B (mod p) for some/any g (and which g);
#  (3) reports the fraction of defects satisfying the relation, and what
#      g precisely is, to ground the leak claim numerically.
#
# Save: scripts/probes/probe_407_laneF_crossparity_leak.py  (do not git add)

from itertools import combinations

def primitive_root_of_order(n, p):
    """Return g in F_p of exact multiplicative order n (needs n | p-1)."""
    assert (p - 1) % n == 0
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1:  # order exactly n (n even)
            return g
    raise RuntimeError("no primitive n-th root")

def find_spurious(n, p, sizes):
    """All antipodal-free index-sets cfg subset {0..n-1} with sum u = sum u^3 = 0 mod p.
       Return list of (cfg_tuple, us_list) where us = [mu^j for j in cfg]."""
    g = primitive_root_of_order(n, p)
    mu = [pow(g, j, p) for j in range(n)]
    half = n // 2
    out = []
    for size in sizes:
        for cfg in combinations(range(n), size):
            cs = set(cfg)
            # antipodal-free: j and j+half not both present
            if any(((j + half) % n) in cs for j in cfg):
                continue
            us = [mu[j] for j in cfg]
            s1 = sum(us) % p
            s3 = sum(pow(u, 3, p) for u in us) % p
            if s1 == 0 and s3 == 0:
                out.append((cfg, us))
    return g, mu, out

def half_sum(idxs, mu, p):
    return sum(mu[j] for j in idxs) % p

def test_crossparity(n, p, sizes):
    g, mu, spur = find_spurious(n, p, sizes)
    half = n // 2
    print(f"\n##### n={n}, p={p} (p mod n = {p % n}), g={g}, sizes={sizes}")
    print(f"  #spurious antipodal-free configs (sum u = sum u^3 = 0): {len(spur)}")
    if not spur:
        print("  (none) -- non-saturated regime, no defects to analyse")
        return

    # Candidate splittings of a config cfg (index list) into (A_idx, B_idx).
    # We try several and, for each config & splitting, look for g0 with A = -g0*B,
    # i.e. A/B = -g0.  Since A,B are field elements, g0 = -A * B^{-1} (mod p) ALWAYS
    # exists if B != 0; so the *content* of the leak claim is that g0 is FIXED
    # (the same ring element across defects), or lies in mu_n, or is structured.
    # We report the distribution of g0 = -A/B for each splitting.

    def split_parity(cfg):
        A = [j for j in cfg if j % 2 == 0]
        B = [j for j in cfg if j % 2 == 1]
        return A, B

    def split_lowhigh(cfg):
        # below/above n/2 in index
        A = [j for j in cfg if j < half]
        B = [j for j in cfg if j >= half]
        return A, B

    def split_firsthalf(cfg):
        # first half of the sorted index list vs second half
        s = sorted(cfg)
        k = len(s) // 2
        return s[:k], s[k:]

    splittings = {
        "parity(index)": split_parity,
        "low/high(index<n/2)": split_lowhigh,
        "first/second half of list": split_firsthalf,
    }

    for name, fn in splittings.items():
        g0_list = []
        ratio_in_mun = 0
        sumA_eq_zero = 0
        sumB_eq_zero = 0
        for cfg, us in spur:
            A_idx, B_idx = fn(cfg)
            A = half_sum(A_idx, mu, p)
            B = half_sum(B_idx, mu, p)
            if B == 0:
                if A == 0:
                    sumA_eq_zero += 1
                    sumB_eq_zero += 1
                continue
            g0 = (-A * pow(B, p - 2, p)) % p   # the unique g0 with A = -g0*B
            g0_list.append(g0)
            # is g0 in mu_n?
            if pow(g0, n, p) == 1:
                ratio_in_mun += 1
        if not g0_list:
            print(f"  [{name}] all B=0 (degenerate); A=0 too: {sumA_eq_zero}/{len(spur)}")
            continue
        distinct = set(g0_list)
        print(f"  [{name}] g0 = -A/B  over {len(g0_list)} defects: "
              f"#distinct g0 = {len(distinct)}; g0 in mu_n: {ratio_in_mun}/{len(g0_list)}")
        # report most common g0 and whether a single fixed g works for >=96%
        from collections import Counter
        c = Counter(g0_list)
        top, topcount = c.most_common(1)[0]
        print(f"      most common g0 = {top}  (covers {topcount}/{len(g0_list)} "
              f"= {100*topcount/len(g0_list):.1f}%)"
              + (f"  [order of g0 mod p = {mult_order(top,p)}]" if top not in (0,1) else ""))

def mult_order(a, p):
    if a % p == 0:
        return None
    o = 1
    x = a % p
    while x != 1:
        x = (x * a) % p
        o += 1
        if o > p:
            return None
    return o

if __name__ == "__main__":
    # The canonical n=64,p=2113 saturated defect locus, plus n=16/p=17, n=32/p=97.
    test_crossparity(16, 17, [4, 6, 8])
    test_crossparity(32, 97, [4, 6])
    test_crossparity(64, 2113, [6])
