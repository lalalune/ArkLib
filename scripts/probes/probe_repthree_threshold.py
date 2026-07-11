#!/usr/bin/env python3
"""
PROBE: does RepThree(mu_n) hold above the six-term threshold p > 12^{n/4}?

RepThree(G): every zero-sum 6-tuple c in G^6 admits a perfect matching sigma of the 6 positions
with c(sigma i) = -c i for all i  (antipodal pairing).

We test PROPER thin mu_n = 2-power subgroup of F_p^*, p == 1 mod n, p >> n^3 (prize regime),
multiple structured primes incl. Fermat-type. NEVER n = p-1.

For each zero-sum 6-tuple (value-multiset over mu_n), check if it is antipodally pairable:
the value-multiset must be partitionable into 3 antipodal pairs {z, -z} (z=0 allowed only if 0 in
mu_n, but 0 not in mu_n so all entries nonzero -> need z != 0, pair z with -z).
A 6-multiset is antipodally pairable iff for every value z, count(z) and count(-z) allow a perfect
matching: specifically the multiset is a disjoint union of pairs {z,-z}. Equivalent: there is a way
to match positions s.t. matched values are negatives. For a multiset this holds iff we can pick a
sub-multiset structure: count(z) = count(-z) is NOT required per-value (a value could pair within
itself only if z = -z i.e. z=0). For z != -z, each z must pair with a -z, so we need, restricted to
the orbit {z,-z}: count(z) + count(-z) even AND can be split into pairs -> always count(z)==count(-z)
because each pair uses one z and one -z. WAIT: a pair is one position with value z and one with -z.
So #pairs using orbit = count(z) (each consumes one z, one -z) => REQUIRES count(z)==count(-z).
So antipodal-pairable (no zero) <=> for all z, count(z) == count(-z).  [matches _E3NegSymConverse]

So RepThree fails iff EXISTS a zero-sum 6-tuple with some z: count(z) != count(-z).
We search for a zero-sum 6-multiset of mu_n that is NOT count-antipodal-balanced.
If none exists for p > threshold => RepThree holds (probe PASS). If one exists => contrapositive
FAILS, log the witness (honest wall).
"""
import itertools, sys
from sympy import isprime

def mu_n(p, n):
    # subgroup of order n in F_p^*; p == 1 mod n. generator g = h^((p-1)/n) for primitive root h.
    # find an element of order exactly n.
    # simple: find g with g^n=1 and g^(n/2)!=1 (n a 2-power so order n iff g^(n/2)!=1)
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and pow(cand, n//2, p) != 1:
            g = cand
            break
    else:
        return None
    S = [pow(g, k, p) for k in range(n)]
    return sorted(set(S))

def count_balanced(combo, p):
    from collections import Counter
    c = Counter(combo)
    for z in c:
        negz = (-z) % p
        if c[z] != c.get(negz, 0):
            return False
    return True

def test(p, n):
    G = mu_n(p, n)
    if G is None or len(G) != n:
        return ("skip", None)
    Gset = G
    # enumerate zero-sum 6-multisets (combinations_with_replacement keeps it a multiset)
    bad = None
    total_zs = 0
    for combo in itertools.combinations_with_replacement(Gset, 6):
        if sum(combo) % p == 0:
            total_zs += 1
            if not count_balanced(combo, p):
                bad = combo
                break
    return ("done", (total_zs, bad))

def main():
    # thin prize-regime: n=4,8 (n=16 too big for combos_w_repl C(16+5,6)~54k * but values... fine for n<=8)
    cases = []
    # n=4: need p==1 mod 4, p > 12^{4/4}=12, p >> n^3=64. threshold 12^{n/4}=12^1=12.
    # n=8: p==1 mod 8, threshold 12^{8/4}=12^2=144, p >> 512.
    for n in (4, 8):
        thr = 12 ** (n // 4)
        primes = []
        cand = max(thr, n**3) + 1
        while len(primes) < 4:
            if isprime(cand) and (cand - 1) % n == 0:
                primes.append(cand)
            cand += 1
        # add a Fermat-type structured prime if applicable
        for fp in (257, 65537):
            if (fp - 1) % n == 0 and fp > thr and fp not in primes:
                primes.append(fp)
        cases.append((n, thr, primes))

    any_fail = False
    for n, thr, primes in cases:
        print(f"=== n={n} (thin 2-power mu_n), six-term threshold 12^(n/4)={thr} ===")
        for p in primes:
            status, res = test(p, n)
            if status == "skip":
                print(f"  p={p}: SKIP (no order-{n} subgroup)")
                continue
            total_zs, bad = res
            above = p > thr
            if bad is None:
                print(f"  p={p} (>{thr}? {above}): {total_zs} zero-sum 6-tuples, ALL count-balanced "
                      f"=> RepThree HOLDS")
            else:
                any_fail = True
                print(f"  p={p} (>{thr}? {above}): UNBALANCED zero-sum witness {bad} "
                      f"=> RepThree FAILS")
    print()
    if any_fail:
        print("VERDICT: RepThree does NOT hold above threshold for some instance "
              "(contrapositive needs care / FAILS). See witnesses.")
    else:
        print("VERDICT: RepThree HOLDS at every tested prime > 12^(n/4) over PROPER thin mu_n. "
              "Contrapositive is SUPPORTED. PASS.")

if __name__ == "__main__":
    main()
