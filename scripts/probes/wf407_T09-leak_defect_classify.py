#!/usr/bin/env python3
"""
wf407_T09-leak_defect_classify.py  --  #407 thread T09-leak, definitive leak reproduction.

Reproduce the "96-100% of mod-q defects obey A == -g B" measurement and turn it into a
count attempt.  A mod-p DEFECT at depth r is a spurious balanced relation
   x_1 + ... + x_r == y_1 + ... + y_r  (mod p),  all in mu_n,
that is NOT a char-0 identity.  We classify EACH defect by its PARITY structure:
   each exponent a in {0..n-1} has parity a mod 2 (even = in mu_{n/2}; odd = in g*mu_{n/2}, g=h).
We test the cross-parity-leak HYPOTHESES:
  (H1) "one-sided parity split": the defect can be written so that ALL of the left side has
       even exponents (in mu_{n/2}) and ALL of the right side has odd exponents (in g*mu_{n/2}),
       i.e. A in S0, B in g*S0 -- the C042 form A == -g0 B' with B = h B', so A == h B'.
  (H2) "balanced-parity": #even exponents on each side equal (weaker).
  (H3) the literal scalar relation: does there exist a SINGLE unit t with
       (sum over A) == t * (sum over A') for the two char-0-distinct multisets?  (t is the
       'g'; for a genuine collision A==B mod p we trivially have t=1, so this is only
       informative for the SUPPORT/dilate reading -- already tested 0% in the other probe.)

We work at the smallest prize-shaped prime where defects appear for the chosen (n,r), and
report the fraction matching each hypothesis, plus the distribution of parity-signatures.
"""
import math, itertools, cmath
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    return None

def smallest_prime_1_mod(n, lo):
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    S = [pow(h, i, p) for i in range(n)]
    return S, h

def char0_key(exps, n):
    w = 2*math.pi/n
    z = sum(cmath.exp(1j*w*a) for a in exps)
    return (round(z.real, 6), round(z.imag, 6))

def find_defects(p, n, S, r, cap=20000):
    """All defect PAIRS (A,B) at depth r: same mod-p sum, distinct char-0 sum.  Returns the
    full set of multisets per mod-p-sum bucket that are char-0-spurious so we can also count
    the number of *witness multisets* in spurious buckets."""
    buckets = defaultdict(list)
    for A in itertools.combinations_with_replacement(range(n), r):
        s = 0
        for a in A: s = (s + S[a]) % p
        buckets[s].append(A)
    defects = []          # (A,B) pairs across distinct char0 classes
    spurious_multisets = 0
    spurious_buckets = 0
    for s, lst in buckets.items():
        if len(lst) < 2: continue
        byc0 = defaultdict(list)
        for A in lst: byc0[char0_key(A, n)].append(A)
        if len(byc0) < 2: continue
        spurious_buckets += 1
        spurious_multisets += len(lst)
        keys = list(byc0.keys())
        for i in range(len(keys)):
            for j in range(i+1, len(keys)):
                defects.append((byc0[keys[i]][0], byc0[keys[j]][0]))
                if len(defects) >= cap:
                    return defects, spurious_multisets, spurious_buckets
    return defects, spurious_multisets, spurious_buckets

def parity_sig(A):
    return tuple(sorted(a % 2 for a in A))

def classify(A, B):
    pa = [a % 2 for a in A]; pb = [b % 2 for b in B]
    # H1 one-sided: one multiset all-even and the other all-odd (in either order)
    A_even = all(x == 0 for x in pa); A_odd = all(x == 1 for x in pa)
    B_even = all(x == 0 for x in pb); B_odd = all(x == 1 for x in pb)
    h1 = (A_even and B_odd) or (A_odd and B_even)
    # H2 balanced parity: same number of odd exponents on each side
    h2 = (sum(pa) == sum(pb))
    return h1, h2

def main():
    print("="*110)
    print("T09-leak  defect parity-classification  (reproduce the 96-100% cross-parity leak)")
    print("="*110)
    for n in (16, 32, 64):
        print(f"\n############  n={n}  ############")
        found = False
        for r in (2, 3, 4, 5):
            ncombo = math.comb(n+r-1, r)
            if ncombo > 1_200_000:
                continue
            # smallest prime 1 mod n that ADMITS defects: scan a few primes from small upward
            for kp, base in enumerate([2*n+1, 8*n, 64*n, 512*n, 4096*n]):
                p = smallest_prime_1_mod(n, base)
                S, h = subgroup(p, n)
                defs, spm, spb = find_defects(p, n, S, r)
                if defs:
                    nd = len(defs)
                    h1c = h2c = 0
                    for (A,B) in defs:
                        a,b = classify(A,B)
                        h1c += a; h2c += b
                    sigs = Counter(parity_sig(A)+('|',)+parity_sig(B) for (A,B) in defs)
                    print(f"  r={r} p={p} (2^{math.log2(p):.1f}) combos={ncombo}: "
                          f"#defectPairs(<=cap)={nd} spuriousBuckets={spb} "
                          f"H1(one-sided parity)={100*h1c/nd:.1f}% "
                          f"H2(balanced parity)={100*h2c/nd:.1f}%")
                    found = True
                    break
            if found:
                break
        if not found:
            print("  (no enumerable defects found at small depths)")
    print("\n" + "="*110)
    print("H1 ~ 100% would confirm the literal 'A in mu_{n/2}, B in g*mu_{n/2}' cross-parity leak.")
    print("H2 measures the weaker balanced-parity invariant.")

if __name__ == "__main__":
    main()
