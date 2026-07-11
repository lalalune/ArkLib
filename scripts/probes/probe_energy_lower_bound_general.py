#!/usr/bin/env python3
"""
probe_energy_lower_bound_general.py  (#444)

DECISIVE one-sweep probe for the GENERAL-r char-p energy LOWER bound (the 0 <= W_r half of
the F5 squeeze), via the count-injection mechanism:

  negSymCount G (2r)  <=  rEnergy G r        (the OPEN claim, char-p UNCONDITIONAL)

equivalently, writing E_r(F_p) = rEnergy(mu_n) r and E0_r = the char-0 closed form
(= negSymCount(mu_n) (2r), the count-balanced 2r-tuple census):

  W_r := E_r(F_p) - E0_r  >=  0    for EVERY r, EVERY p.

This is the LOWER half of the _BchksF5 squeeze 0 <= W_r <= Wick_r - E0_r (F5 proves only the
UPPER half via the open below-Wick hypothesis; the lower half 0 <= W_r is STATED but never proven).
The mechanism: every count-balanced 2r-tuple is a genuine zero-sum 2r-tuple (char-free converse),
and rEnergy G r = #{zero-sum 2r-tuples} (char-free bijection). So the count-balanced tuples INJECT
into the energy -> E_r >= (their count) = E0_r, UNCONDITIONALLY in char p.

PROBE RULES: PROPER thin mu_n = 2^a (a>=2), p = 1 mod n so n | p-1, NEVER n = q-1, large primes
p >> n^3 AND small primes p (to exercise the extra-collision surplus), multiple primes incl
Fermat-type. r = 2,3,4 (depth-4 = the F5 r=4 case + beyond).
"""

def mu_n(p, n):
    # the order-n subgroup of F_p^* : { g^((p-1)//n) ... } -> collect all x with x^n == 1
    return [x for x in range(1, p) if pow(x, n, p) == 1]

def rEnergy(G, p, r):
    # #{(v,w) in G^r x G^r : sum v = sum w mod p}, by the |hat count|: count residues
    # use the count: sum over residue s of (#{v in G^r : sum v = s})^2
    from collections import Counter
    # build distribution of r-fold sums
    sums = Counter()
    def rec(depth, acc):
        if depth == r:
            sums[acc % p] += 1
            return
        for g in G:
            rec(depth + 1, acc + g)
    rec(0, 0)
    return sum(c * c for c in sums.values())

def negSymCount(G, p, m):
    # #{c in G^m : value-fibers antipodally balanced: #{i:c_i=z} = #{i:c_i=-z} for all z}
    # = count-balanced tuples. Enumerate m-tuples (m=2r small here).
    from itertools import product
    from collections import Counter
    cnt = 0
    negmap = {z: (p - z) % p for z in G}
    for tup in product(G, repeat=m):
        fib = Counter(tup)
        ok = True
        for z in G:
            if fib.get(z, 0) != fib.get((p - z) % p, 0):
                ok = False
                break
        if ok:
            cnt += 1
    return cnt

def first_prime_1modn(n, lo):
    from sympy import isprime
    q = lo - (lo % n) + 1
    if q <= lo:
        q += n
    while True:
        if q > 1 and isprime(q):
            return q
        q += n

def main():
    print("r  n   p        E_r(F_p)=rEnergy   E0_r=negSymCount(2r)   W_r=E_r-E0_r   >=0?  p>n^3?")
    print("-" * 92)
    fails = 0
    total = 0
    # keep enumeration tractable: negSymCount enumerates n^(2r) tuples.
    cases = [
        # (n, r, list of primes)  -- small enough that n^(2r) is enumerable
        (4, 2, None), (4, 3, None), (4, 4, None),
        (8, 2, None), (8, 3, None),
        (16, 2, None),
    ]
    for (n, r, _) in cases:
        m = 2 * r
        if n ** m > 6_000_000:   # cap enumeration of negSymCount tuples
            continue
        # primes: one small (extra-collision regime p < n^3) + one large (p >> n^3) + a Fermat-type
        smallp = first_prime_1modn(n, n + 1)
        largep = first_prime_1modn(n, n ** 4)
        plist = sorted(set([smallp, largep]))
        for p in plist:
            G = mu_n(p, n)
            if len(G) != n:
                continue
            Er = rEnergy(G, p, r)
            E0 = negSymCount(G, p, m)
            Wr = Er - E0
            total += 1
            ok = Wr >= 0
            if not ok:
                fails += 1
            print(f"{r}  {n:<3} {p:<8} {Er:<18} {E0:<22} {Wr:<14} {str(ok):<5} {p > n**3}")
    print("-" * 92)
    print(f"VERDICT: {total - fails}/{total} satisfy W_r >= 0 (E_r(F_p) >= E0_r), "
          f"the char-p UNCONDITIONAL energy lower bound.")
    print(f"  fails: {fails}.  (W_r = 0 expected exactly when p > n^3 = no extra collisions;")
    print(f"   W_r > 0 at small p = the extra-collision surplus, still >= 0 => lower bound holds.)")

if __name__ == "__main__":
    main()
