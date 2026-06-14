#!/usr/bin/env python3
"""Probe (#389): the EXACT list at agreement exactly rm — are valid R fibre-unions?

For the ladder word w = x^{rm} + lam*x^{(r-1)m}, code dim k = (r-2)m+1, a codeword
c = eval(P) (deg P <= (r-2)m) has agreement EXACTLY rm with w iff
    D(X) = X^{rm} + lam*X^{(r-1)m} - P(X)
splits completely over the domain <g>, i.e. D = prod_{x in R}(X - x) for an
rm-subset R of <g>.  Matching coefficients (deg P <= (r-2)m) forces the GAP pattern
    e_1(R) = ... = e_{m-1}(R) = 0,  e_m(R) = (-1)^m lam,
    e_{m+1}(R) = ... = e_{2m-1}(R) = 0.
(Lower e's are free = the codeword P.)

The fibre-unions R_T = {x : x^m in T} (T an r-subset of mu_s with sum T = -lam) are
special valid R (D_T = prod_{a in T}(X^m - a), a polynomial in X^m).

DECISIVE QUESTION: is EVERY valid R a fibre-union (a union of cosets of <g^s>)?
 - If yes at all scales -> the agreement-rm list = N_fib EXACTLY, provable, no wall.
 - If some valid R is NOT a coset-union -> the exact list exceeds N_fib; report it.

We enumerate ALL rm-subsets R of <g>, test the gap conditions, count them, and check
coset-closure.  Compared against N_fib = #{r-subsets T of mu_s : sum T = -lam}.
"""
import itertools, sys
from collections import Counter


def find_g(p, n):
    for h in range(2, 2000):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    return None


def esym(R, p):
    """elementary symmetric functions e_0..e_|R| of multiset R mod p."""
    e = [1]
    for x in R:
        ne = e + [0]
        for i in range(len(e), 0, -1):
            ne[i] = (ne[i] + x * e[i - 1]) % p
        e = ne
    return e


def run(N, m, r, p):
    g = find_g(N=N, p=p) if False else find_g(p, N)
    if g is None:
        print(f"(no order-{N} mod {p})"); return
    dom = [pow(g, i, p) for i in range(N)]
    s = N // m
    assert s * m == N
    K = (r - 2) * m + 1
    a = r * m
    # mu_s = m-power subgroup; coset structure: kernel = <g^s> (order m)
    ker = sorted({pow(g, s * i, p) for i in range(m)})  # order-m subgroup
    assert len(ker) == m
    mus = sorted({pow(x, m, p) for x in dom})
    assert len(mus) == s
    # N_fib over ALL lambda
    fib = Counter()
    for T in itertools.combinations(mus, r):
        fib[sum(T) % p] += 1   # this is e_1(T); lam = -sum T
    # enumerate valid R for the GLOBAL question: for each lambda, count valid R
    # group valid R by their e_m value (= (-1)^m lam) and check the gap zeros
    sign = (-1) ** m % p
    validR_by_lam = Counter()
    noncoset_examples = []
    # coset membership test: R is coset-union iff for every x in R, all of x*ker in R
    Rset_all = list(itertools.combinations(range(N), a))
    for Ridx in Rset_all:
        R = [dom[i] for i in Ridx]
        e = esym(R, p)
        # gap conditions: e_1..e_{m-1}=0, e_{m+1}..e_{2m-1}=0
        ok = all(e[j] == 0 for j in range(1, m)) and \
             all(e[j] == 0 for j in range(m + 1, min(2 * m, a + 1)))
        if not ok:
            continue
        em = e[m] if m <= a else 0
        lam = (sign * em) % p  # e_m = (-1)^m lam  ->  lam = (-1)^m e_m
        validR_by_lam[lam] += 1
        # coset-closure check
        Rs = set(R)
        is_coset = all((x * d) % p in Rs for x in R for d in ker)
        if not is_coset:
            noncoset_examples.append((Ridx, lam))
    # compare per-lambda: valid R count vs N_fib(lambda)
    print(f"\n==== n={N}, m={m}, r={r}, k={K}, a=rm={a}, p={p} (s={s}) ====", flush=True)
    print(f"  N_fib (max over lam) = {max(fib.values())}; "
          f"#distinct lam with fibre = {len(fib)}", flush=True)
    print(f"  valid-R count (max over lam) = {max(validR_by_lam.values()) if validR_by_lam else 0}; "
          f"#distinct lam with valid R = {len(validR_by_lam)}", flush=True)
    # per-lambda exact comparison
    mismatch = 0
    for lam in set(list(fib.keys()) + list(validR_by_lam.keys())):
        # fibre count at this lam = #{T : -sum T = lam} = fib[(-lam) % p]
        fcount = fib.get((-lam) % p, 0)
        vcount = validR_by_lam.get(lam, 0)
        if fcount != vcount:
            mismatch += 1
            if mismatch <= 5:
                print(f"    lam={lam}: fibre {fcount} vs validR {vcount}  <-- MISMATCH",
                      flush=True)
    print(f"  per-lambda mismatches (fibre vs validR): {mismatch}", flush=True)
    print(f"  non-coset valid R found: {len(noncoset_examples)}", flush=True)
    if mismatch == 0 and len(noncoset_examples) == 0:
        print("  VERDICT: agreement-rm list = N_fib EXACTLY; every valid R is a "
              "coset-union -> PROVABLE exact law at agreement rm.", flush=True)
    elif len(noncoset_examples) > 0:
        print(f"  VERDICT: NON-COSET valid R EXISTS (e.g. {noncoset_examples[0]}) "
              "-> exact list may exceed fibre; structural lead.", flush=True)
    else:
        print("  VERDICT: counts match but coset-closure subtle; investigate.",
              flush=True)


def main():
    # n=16: m=2,r=3 (a=6, C(16,6)=8008); m=4,r=2 (a=8, C(16,8)=12870)
    run(16, 2, 3, 12289)
    run(16, 2, 3, 7681)   # second prime
    run(16, 4, 2, 12289)
    # n=12: m=2,r=3 would need s=6 ... n=12 m=3 r=2? a=6, k=1. try m=2,r=3? s=6.
    run(12, 2, 3, 13)     # tiny char check (p=13, order 12)
    return 0


if __name__ == "__main__":
    sys.exit(main())
