"""PROBE (#444 census face): the RS monomial far-line bad-scalar set (explainableScalars) on a
THIN proper subgroup mu_n is closed under mult by m=g^(A-B) (scalardil landed). Does its CARDINALITY
divide by ord(m)=n/gcd(A-B,n)? And is 0 ever bad (orbits have full size ord(m) iff 0 excluded)?

explainableScalars def: gamma bad iff exists deg<k RS codeword w with
  #{i : u0_i + gamma*u1_i = w_i} >= ceil((1-delta)*n).  Monomial line u0=x^B, u1=x^A on mu_n.
THIN proper: n=2^a, (p-1)/n>=2 (NEVER n=q-1), large p incl Fermat 17/257. delta mid-window.
"""
import itertools
import math


def find_subgroup(p, n):
    if (p - 1) % n != 0:
        return None
    g = None
    for cand in range(2, p):
        pows = [pow(cand, j, p) for j in range(1, n + 1)]
        if pows[-1] == 1 and all(pows[j] != 1 for j in range(n - 1)):
            g = cand
            break
    if g is None:
        return None
    mu = sorted(set(pow(g, j, p) for j in range(n)))
    return g, mu


def rs_codewords(domain, k, p):
    for coeffs in itertools.product(range(p), repeat=k):
        yield tuple(sum(coeffs[d] * pow(x, d, p) for d in range(k)) % p for x in domain)


def explainable(domain, k, A, B, delta, p):
    n = len(domain)
    need = math.ceil((1.0 - delta) * n)
    u0 = [pow(x, B, p) for x in domain]
    u1 = [pow(x, A, p) for x in domain]
    cws = list(rs_codewords(domain, k, p))
    bad = set()
    for gamma in range(p):
        line = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
        for w in cws:
            agree = sum(1 for i in range(n) if line[i] == w[i])
            if agree >= need:
                bad.add(gamma)
                break
    return bad


configs = [
    (17, 4, 2, 3, 1),
    (41, 8, 2, 3, 1),
    (41, 8, 2, 5, 2),
    (113, 8, 2, 5, 1),
    (97, 4, 2, 3, 1),
    (73, 8, 2, 3, 1),
    (17, 8, 2, 3, 1),
    (41, 4, 2, 3, 1),
]
results = []
for (p, n, k, A, B) in configs:
    delta = 0.5
    sg = find_subgroup(p, n)
    if sg is None:
        print("SKIP p=%d n=%d (no subgroup)" % (p, n))
        continue
    g, mu = sg
    if (p - 1) // n < 2:
        print("SKIP p=%d n=%d FULL GROUP" % (p, n))
        continue
    bad = explainable(mu, k, A, B, delta, p)
    d = n // math.gcd(A - B, n)
    has0 = (0 in bad)
    card = len(bad)
    nz = card - (1 if has0 else 0)
    nz_div = (nz % d == 0)
    print("p=%d n=%d k=%d A=%d B=%d ord(m)=%d |bad|=%d 0in=%s card%%d=%d nz%%d=%d NZdiv=%s"
          % (p, n, k, A, B, d, card, has0, card % d, nz % d, nz_div))
    results.append(nz_div)
print("ALL nonzero-part divisible by ord(m): %s (%d/%d)"
      % (all(results), sum(results), len(results)))
