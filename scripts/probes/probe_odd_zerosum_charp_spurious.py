#!/usr/bin/env python3
"""
PROBE (#444): the ODD-order zeroSumCount of the thin 2-power subgroup mu_n over F_q.

In char 0 (C), zeroSumCount(mu_{2^k}, r) = 0 for ALL odd r (proven, in-tree
OddZeroSumCountVanishCharZero.zeroSumCount_odd_dyadicRoots_eq_zero).

QUESTION: over F_q (prize-regime thin mu_n, n=2^a, q>>n^3 incl Fermat), for odd r:
  (A) is zeroSumCount(mu_n, r) over F_q generally NONZERO?
  (B) is it EXACTLY the count of r-tuples t:Fin r -> mu_n with sum_F_q t = 0 BUT whose
      char-0 lift sum_C lift(t) != 0 ? i.e. supported ENTIRELY on char-p spurious collisions
      (the lift of every F_q zero-sum odd-tuple is a char-0 NON-zero-sum tuple, since char-0
      odd zero-sum count is 0). => oddZeroSumCount_F_q = #{spurious odd zero-sum tuples}.

This LOCATES the entire odd-order prize signal in the spurious set, axiom-cleanly testable.

Discipline: PROPER thin subgroup mu_n = <g^((p-1)/n)> (n=2^a, (p-1)/n >= 2), NEVER n=q-1.
Multiple primes incl p >> n^3 and Fermat-type. Exact arithmetic.
"""
import itertools

def primfind(n, lo, count=3):
    """smallest `count` primes p == 1 mod n with p > lo."""
    out = []
    # start search above lo, step through p == 1 mod n
    k = (lo // n) + 1
    while len(out) < count:
        p = k * n + 1
        if p > lo and is_prime(p):
            out.append(p)
        k += 1
    return out

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = 3
    while d * d <= m:
        if m % d == 0: return False
        d += 2
    return True

def prim_root(p):
    """a primitive root mod p (p prime)."""
    phi = p - 1
    # factor phi
    fac = []
    m = phi; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in fac):
            return g
    raise RuntimeError("no primitive root")

def mu_n_subgroup(p, n):
    """thin 2-power subgroup mu_n = <g^((p-1)/n)> as a list of residues mod p."""
    assert (p - 1) % n == 0
    g = prim_root(p)
    h = pow(g, (p - 1) // n, p)  # generator of order n
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x * h) % p
    assert len(set(elts)) == n, "not order n"
    return elts, g

def roots_of_unity_C(n):
    """exact-ish complex n-th roots of unity (for char-0 zero-sum test)."""
    import cmath
    return [cmath.exp(2j * cmath.pi * j / n) for j in range(n)]

def char0_zero_sum(tuple_idx, roots_c, tol=1e-9):
    """does the C-lift of the index-tuple sum to 0?"""
    s = sum(roots_c[i] for i in tuple_idx)
    return abs(s) < tol

def zerosum_count_fq(p, n, r):
    """
    zeroSumCount over F_q (here F_p, q=p): #{t:Fin r -> mu_n : sum_F_p t = 0}.
    Also splits into char-0-vanishing vs spurious (char-0-nonvanishing) parts,
    using a CONSISTENT index<->root correspondence (mu_n elements <-> n-th roots
    of unity by discrete-log order: mu_n[j] = h^j  <->  zeta_n^j).
    """
    elts, g = mu_n_subgroup(p, n)
    roots_c = roots_of_unity_C(n)  # roots_c[j] <-> elts[j] (both = (.)^j of order-n gen)
    total = 0
    spurious = 0   # F_p zero-sum but C-NONzero  (char-p-only collision)
    genuine = 0    # F_p zero-sum AND C-zero      (should be 0 for odd r)
    for tup in itertools.product(range(n), repeat=r):
        s = sum(elts[i] for i in tup) % p
        if s == 0:
            total += 1
            if char0_zero_sum(tup, roots_c):
                genuine += 1
            else:
                spurious += 1
    return total, genuine, spurious

def main():
    print("# ODD-order zeroSumCount of thin mu_n over F_p (prize regime)")
    print("# char-0 odd zeroSumCount == 0 (proven). Testing F_p decomposition.")
    print("# cols: n  p  r  | total_FpZS  genuine(C-zero)  spurious(C-nonzero)  p>n^3?")
    print("# CLAIM under test: genuine==0 (all odd F_p zero-sums are char-p SPURIOUS)")
    any_genuine = False
    rows = 0
    for a in (2, 3, 4):           # n = 4, 8, 16
        n = 2 ** a
        # primes: a small p==1 mod n with (p-1)/n>=2, a big p>>n^3, and try a Fermat-ish one
        cand = primfind(n, n, count=2) + primfind(n, n**3, count=2)
        # Fermat F_3 = 257 (==1 mod 16,8,4), F_4=65537
        for fp in (257, 65537):
            if (fp - 1) % n == 0 and fp not in cand:
                cand.append(fp)
        for p in sorted(set(cand)):
            if (p - 1) // n < 2:    # must be PROPER thin subgroup, never n=q-1
                continue
            for r in (3, 5):        # odd orders
                # cap blowup: n^r tuples; skip if too large
                if n ** r > 3_000_000:
                    continue
                total, genuine, spurious = zerosum_count_fq(p, n, r)
                big = "YES" if p > n**3 else "no"
                flag = "  <== GENUINE!=0!!" if genuine != 0 else ""
                if genuine != 0:
                    any_genuine = True
                print(f"  n={n:3d} p={p:6d} r={r} | tot={total:6d} "
                      f"genuine={genuine:5d} spur={spurious:6d}  p>n^3={big}{flag}")
                rows += 1
    print(f"\n# rows={rows}  any_genuine_nonzero={any_genuine}")
    if not any_genuine:
        print("# VERDICT: every odd-order F_p zero-sum of mu_n is char-p SPURIOUS "
              "(C-lift nonzero). => oddZeroSumCount_F_p == #spurious-odd-zero-sum-tuples.")
        print("# The entire odd-order prize signal lives in the char-p spurious set. CONFIRMS")
        print("# the char-0 vanishing brick's prose + makes it an F_p IDENTITY candidate.")
    else:
        print("# VERDICT: counterexample to 'odd F_p zero-sum => char-p spurious'. Re-examine.")

if __name__ == "__main__":
    main()
