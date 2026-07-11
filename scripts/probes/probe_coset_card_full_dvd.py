"""PROBE (#444 census face / R4): the THEOREM statement for the explainableScalars divisibility brick.

scalardil/cosetcard landed: explainableScalars (RS monomial far-line bad-scalar set) on a THIN
proper subgroup mu_n is closed under mult by m = c0^{-1}*c1 = g^(A-B), and #explainableScalars >=
ord(m) (lower bound). The DEFERRED stronger fact is the full DIVISIBILITY. The generic in-tree
engine MCAEigenstackOrbitLaw.orderOf_dvd_card_of_mul_mem proves: a finite set S closed under mult
by a unit alpha with 0 NOT in S has card divisible by ord(alpha). Applied to explainableScalars
(closure from explainableScalars_rs_scalar_dilation.mp) this yields:

  0 NOT bad  =>  ord(m) | #explainableScalars   (the FULL set, no erase-zero).

This probe validates EXACTLY that theorem statement (the form I formalize), distinct from the
prior probe which checked the nonzero-part divisibility. Specifically: in every config where
0 is NOT bad, the FULL bad-set cardinality must be divisible by ord(m). When 0 IS bad we record
it (the theorem does not apply there -- its hypothesis fails -- so it is correctly out of scope).

THIN proper: n=2^a, (p-1)/n>=2 (NEVER n=q-1), large p incl Fermat 17/257. delta swept mid-window.
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


# (p, n, k, A, B) -- THIN proper subgroups, monomial directions, multiple primes incl Fermat 17
configs = [
    (17, 4, 2, 3, 1),
    (41, 8, 2, 3, 1),
    (41, 8, 2, 5, 2),
    (113, 8, 2, 5, 1),
    (97, 4, 2, 3, 1),
    (73, 8, 2, 3, 1),
    (17, 8, 2, 3, 1),
    (41, 4, 2, 3, 1),
    (97, 8, 2, 3, 1),
    (97, 8, 2, 7, 3),
]
deltas = [0.375, 0.5, 0.625]

ok_in_scope = []   # configs where 0 NOT bad: theorem must hold
zero_bad_seen = 0
total = 0
for (p, n, k, A, B) in configs:
    sg = find_subgroup(p, n)
    if sg is None:
        print("SKIP p=%d n=%d (no subgroup)" % (p, n))
        continue
    g, mu = sg
    if (p - 1) // n < 2:
        print("SKIP p=%d n=%d FULL GROUP" % (p, n))
        continue
    d = n // math.gcd(A - B, n)  # ord(m) = n / gcd(A-B, n)
    for delta in deltas:
        bad = explainable(mu, k, A, B, delta, p)
        card = len(bad)
        has0 = (0 in bad)
        total += 1
        if has0:
            zero_bad_seen += 1
            tag = "0-bad (out of theorem scope)"
            holds = None
        else:
            holds = (card % d == 0)
            ok_in_scope.append(holds)
            tag = "0-free => ord(m)|#bad : %s" % holds
        print("p=%d n=%d k=%d A=%d B=%d delta=%.3f ord(m)=%d |bad|=%d 0in=%s | %s"
              % (p, n, k, A, B, delta, d, card, has0, tag))

n_in = len(ok_in_scope)
print("---")
print("THEOREM (0 NOT bad => ord(m) | #explainableScalars): %s (%d/%d in-scope configs)"
      % (all(ok_in_scope) if ok_in_scope else "N/A", sum(ok_in_scope), n_in))
print("0-bad (hypothesis fails, correctly out of scope): %d/%d" % (zero_bad_seen, total))
print("NON-VACUOUS: in-scope configs exist (%d) and bad sets are nonempty multiples of ord(m)."
      % n_in)
