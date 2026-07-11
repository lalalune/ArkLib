#!/usr/bin/env python3
"""
probe_short_excess_relation_407.py  (#407)

Verifies the load-bearing c.150/c.151 claim: at prize-regime STRUCTURED primes
there exist SHORT constant-weight excess relations among the 2-power subgroup
mu_n -- i.e. small multisets of roots that vanish mod p but NOT in char 0
(beyond trivial antipodal pairs zeta + (-zeta) = 0).  Their existence makes the
min-weight reduction W(n,p) >= ceil(2 log m) FALSE and hence the moment
certificate GaussianEnergyBound (E_r <= Wick at r ~ log m) NON-PROVING.

A "char-0 trivial" relation = a disjoint union of antipodal pairs {x,-x}.
We search small primes p == 1 mod n (mu_n exists in F_p) for a +/-1 relation
   sum_i eps_i * g^{a_i} == 0  (mod p),  eps_i in {+1,-1}, distinct a_i,
of weight w (number of terms) that is NOT antipodal-decomposable.
"""
import itertools

def find_gen_mu_n(p, n):
    """a generator of the order-n subgroup mu_n in F_p^*  (n | p-1)."""
    assert (p - 1) % n == 0
    for h in range(2, p):
        g = pow(h, (p - 1) // n, p)
        if pow(g, n, p) == 1 and all(pow(g, n // q, p) != 1
                                     for q in (2,) if n % q == 0):
            # order exactly n (n=2^a so only prime factor is 2)
            if pow(g, n // 2, p) != 1:
                return g
    return None

def antipodal_decomposable(terms, n, half):
    """terms = list of (eps, a); is it a disjoint union of {+x,-x} pairs?
    -g^a = g^{a+half}.  So a +x and a -x pair = (+1,a) and (-1,a) OR
    (+1,a) and (+1,a+half) [since -g^a=g^{a+half}], etc.  Normalize each term
    to a 'signed exponent' and pair x with -x."""
    # represent each term as the element value-exponent with sign folded in:
    # eps*g^a = g^a if eps=+1 else g^{a+half}. So signed-exponent s = a (eps+) or a+half (eps-).
    sexps = sorted(((a if e == 1 else (a + half) % n) for e, a in terms))
    used = [False] * len(sexps)
    for i in range(len(sexps)):
        if used[i]:
            continue
        # find j>i with sexps[j] == sexps[i]+half (the antipode)
        target = (sexps[i] + half) % n
        found = False
        for j in range(len(sexps)):
            if not used[j] and j != i and sexps[j] == target:
                used[i] = used[j] = True
                found = True
                break
        if not found:
            return False
    return all(used)

def search(p, n, max_w=6):
    g = find_gen_mu_n(p, n)
    if g is None:
        return None
    half = n // 2
    powers = [pow(g, a, p) for a in range(n)]
    # search +/-1 relations of weight w (try w even, 4 and 6) over distinct exponents
    for w in (4, 6):
        for combo in itertools.combinations(range(n), w):
            # try sign patterns (fix first sign +1 to break global negation)
            for signs in itertools.product((1, -1), repeat=w - 1):
                signs = (1,) + signs
                s = sum(sg * powers[a] for sg, a in zip(signs, combo)) % p
                if s == 0:
                    terms = list(zip(signs, combo))
                    if not antipodal_decomposable(terms, n, half):
                        return (w, terms, g)
    return None

# structured primes p == 1 mod n with high 2-adic valuation (Fermat/Proth-like)
cases = [
    (97, 16), (193, 16), (257, 16), (8161, 16),
    (193, 32), (449, 32), (577, 32),
    (257, 64), (12289, 64),  # 12289 = 3*2^12+1, very high 2-part
    (40961, 128),            # 40961 = 5*2^13+1
]
print(f"{'p':>8} {'n':>5} {'v2(p-1)':>8} {'shortest NON-antipodal excess relation':>45}")
print("-" * 75)
for p, n in cases:
    if (p - 1) % n != 0:
        print(f"{p:>8} {n:>5}    n does not divide p-1 -- skip")
        continue
    v2 = ((p - 1) & -(p - 1)).bit_length() - 1
    r = search(p, n)
    if r is None:
        print(f"{p:>8} {n:>5} {v2:>8}    none of weight <=6 found")
    else:
        w, terms, g = r
        desc = " + ".join(f"{'+' if e>0 else '-'}g^{a}" for e, a in terms)
        print(f"{p:>8} {n:>5} {v2:>8}    weight {w}: {desc} == 0")

print("""
Reading: a non-antipodal +/-1 relation of weight 4 or 6 is a SHORT char-p
excess relation (char 0 forbids vanishing sums of <= such length except
antipodal pairs, Lam-Leung/Mann).  Each such relation is an E_r excess solution
not present in char 0, so E_r^{F_p} > Wick once r reaches that weight -- the
min-weight W(n,p)=O(1) (NOT >= 2 log m), confirming GaussianEnergyBound is
non-proving at structured primes (c.150/c.151).  This is a REFUTATION of the
moment-certificate route, not a path to the prize.
""")
