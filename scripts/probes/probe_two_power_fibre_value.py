#!/usr/bin/env python3
"""#389 probe: THE EXACT SUBSET-SUM FIBRE VALUE AT 2-POWER TOWERS.

Claim (to falsify): for s = 2^h (h >= 2), the subset-sum fibre profile of mu_s over
r-subsets is EXACTLY the antipodal-core formula:

  - every value v attained by an r-subset sum has a unique signed core
    c in {-1,0,1}^(s/2) (coefficients over the half-system 1, z, ..., z^(s/2-1)),
  - the fibre of v has size C(s/2 - u, (r-u)/2) where u = |supp(c)| (parity-matched),
  - hence N_fib(s,r) = C(s/2 - 1, (r-1)/2) for r odd, C(s/2, r/2) for r even.

Arithmetic: EXACT, in Z[x]/(x^(s/2)+1) (= Z[zeta_s], since Phi_{2^h} = x^(s/2)+1).
Also checks the split-prime transfer (fibres over F_p for p = 1 mod s, two primes).
Exit 0 iff every check passes.
"""
import itertools, sys
from math import comb

FAIL = 0
def check(name, ok):
    global FAIL
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        FAIL += 1

def predicted_nfib(s, r):
    if r % 2 == 1:
        return comb(s // 2 - 1, (r - 1) // 2)
    return comb(s // 2, r // 2)

def fibre_profile_char0(s, r):
    """Exact char-0 fibre profile: map value -> count, values in Z[x]/(x^(s/2)+1)."""
    half = s // 2
    # zeta^j for j < s as vector in Z^half: j < half -> e_j ; j >= half -> -e_{j-half}
    from collections import Counter
    fib = Counter()
    for T in itertools.combinations(range(s), r):
        vec = [0] * half
        for j in T:
            if j < half:
                vec[j] += 1
            else:
                vec[j - half] -= 1
        fib[tuple(vec)] += 1
    return fib

print("=" * 70)
print("(A) char-0 exact fibre profiles vs the antipodal-core formula")
for s, rmax in [(8, 6), (16, 5), (32, 4)]:
    half = s // 2
    for r in range(2, rmax + 1):
        fib = fibre_profile_char0(s, r)
        # formula check per value: u = #nonzero entries of the core, all entries in {-1,0,1}
        ok_core = all(all(abs(e) <= 1 for e in v) for v in fib)
        ok_count = True
        for v, cnt in fib.items():
            u = sum(1 for e in v if e != 0)
            expect = comb(half - u, (r - u) // 2) if (r - u) % 2 == 0 and r >= u else 0
            if cnt != expect:
                ok_count = False
                print(f"  MISMATCH s={s} r={r} core-u={u}: count {cnt} != {expect}")
        nmax = max(fib.values())
        pred = predicted_nfib(s, r)
        total = sum(fib.values())
        check(f"s={s} r={r}: cores reduced ({ok_core}), all fibre counts match formula",
              ok_core and ok_count)
        check(f"s={s} r={r}: N_fib = {nmax} = predicted {pred}; total {total} = C({s},{r})",
              nmax == pred and total == comb(s, r))

print("=" * 70)
print("(B) split-prime transfer: fibre profile over F_p (p = 1 mod s), two primes")
def fibre_max_fp(s, r, p):
    # find element of order s in F_p
    from collections import Counter
    for g in range(2, p):
        z = pow(g, (p - 1) // s, p)
        # order check
        o, x = 1, z
        while x != 1:
            x = x * z % p
            o += 1
        if o == s:
            break
    mus = [pow(z, j, p) for j in range(s)]
    fib = Counter()
    for T in itertools.combinations(range(s), r):
        fib[sum(mus[j] for j in T) % p] += 1
    return max(fib.values())

for s, r in [(8, 3), (8, 4), (16, 3), (16, 4), (32, 3)]:
    pred = predicted_nfib(s, r)
    for p in [12289, 65537]:
        if (p - 1) % s != 0:
            continue
        got = fibre_max_fp(s, r, p)
        check(f"s={s} r={r} p={p}: F_p fibre max {got} = char-0 {pred}", got == pred)

print("=" * 70)
print("FAILURES:", FAIL)
sys.exit(0 if FAIL == 0 else 1)
