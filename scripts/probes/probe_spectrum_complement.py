# Probe: deep-band subset-sum spectrum complement symmetry.
# Object: gamma_S = -sum_{z in S} z, S subset of mu_n (thin 2-power subgroup, z!=0).
# Claim (disentanglement (3), lalalune "verified"): the set of gamma values at subset-size r
#   equals the NEGATION of the set at size n-r, hence #distinct(r) = #distinct(n-r).
# Mechanism: sum over ALL of mu_n = 0 (neg-closed), so
#   gamma_{mu\S} = -sum_{mu\S} = -(0 - sum_S) = sum_S = -gamma_S.
# PROPER thin mu_n: n=2^a subgroup of F_p^*, n < p-1 (NEVER full group).
from itertools import combinations


def mu_n_in_Fp(n, p):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        if pow(cand, n, p) == 1:
            ok = True
            for d in range(1, n):
                if n % d == 0 and d < n and pow(cand, d, p) == 1:
                    ok = False
                    break
            if ok:
                g = cand
                break
    assert g is not None, (n, p)
    return [pow(g, i, p) for i in range(n)]


def spectrum_sizes(mu, p):
    n = len(mu)
    res = {}
    for r in range(0, n + 1):
        S = set()
        for comb in combinations(mu, r):
            S.add((-sum(comb)) % p)
        res[r] = S
    return res


def test(n, p):
    mu = mu_n_in_Fp(n, p)
    assert n < p - 1, "must be proper subgroup, never full"
    tot = sum(mu) % p
    spec = spectrum_sizes(mu, p)
    n_ = len(mu)
    fails = 0
    for r in range(0, n_ + 1):
        Sr = spec[r]
        Snr = spec[n_ - r]
        negSnr = set((-x) % p for x in Snr)
        if Sr != negSnr:
            fails += 1
        if len(Sr) != len(Snr):
            fails += 1
    return tot, fails, [len(spec[r]) for r in range(0, min(n_ + 1, 9))]


cases = [
    (8, 41),
    (8, 17),
    (16, 97),
    (16, 257),
    (8, 73),
    (16, 113),
    (16, 1009),
]
allfail = 0
for n, p in cases:
    tot, fails, sizes = test(n, p)
    allfail += fails
    print("n=%3d p=%5d  sum(mu)%%p=%d  fails=%d  #distinct[r=0..]=%s"
          % (n, p, tot, fails, sizes))
print("TOTAL FAILS:", allfail)
