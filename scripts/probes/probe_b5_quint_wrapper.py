#!/usr/bin/env python3
"""
PROBE (rule 2, probe-first) — the 5-element rung of the B_h Sidon depth ladder for mu_n (#444, §0).

Question: for n-th roots of unity, which elementary-symmetric tuple of a 5-multiset forces the
unordered quintuple, and is the missing e_4 supplied FREE by conjugation (so the wrapper need only
hypothesize e_1, e_2, e_3, e_5)?

For |x|=1, conj(x) = 1/x, so conj(e_k) = e_{h-k}/e_h. For h=5:
    conj(e_1) = e_4 / e_5   =>   e_4 = e_5 * conj(e_1)      (e_4 FREE from (e_1, e_5))
    conj(e_2) = e_3 / e_5   =>   e_3 = e_5 * conj(e_2)      (alternative: e_3 free from (e_2,e_5))

Decisive sweeps (exact complex roots of unity, NEVER n=q-1 — these are abstract mu_n, proper thin):
  (A) sum-only (e_1) Sidon?  expect FALSE for h=5.
  (B) (e_1,e_2,e_3,e_5) fixed => unordered quintuple forced?  expect TRUE (e_4 free).
  (C) conjugation identity  e_4 == e_5 * conj(e_1)  exact?  expect maxerr ~1e-13.
  (D) confirm a NON-trivial wrapper: (e_1,e_2,e_5) alone NOT enough (e_3,e_4 both underdetermined).
"""
import itertools, math, cmath, random
random.seed(20260617)

def esymm(xs):
    # returns (e1,e2,e3,e4,e5) for a 5-multiset xs
    e = [0]*6
    e[0] = 1.0
    for x in xs:
        for k in range(5, 0, -1):
            e[k] = e[k] + e[k-1]*x
    return e[1], e[2], e[3], e[4], e[5]

def roots(n):
    return [cmath.exp(2j*math.pi*t/n) for t in range(n)]

def key(z, tol=1e-9):
    return (round(z.real/tol), round(z.imag/tol))

def multiset_key(xs):
    return tuple(sorted(key(x) for x in xs))

def run():
    print("== B5 quintuple Sidon probe ==")
    for n in (5, 6, 8, 10):
        R = roots(n)
        all5 = list(itertools.combinations_with_replacement(range(n), 5))
        # build esymm signatures
        # (A) sum-only collisions
        sumbuckets = {}
        # (B) (e1,e2,e3,e5) buckets
        b1235 = {}
        # (D) (e1,e2,e5) buckets
        b125 = {}
        for combo in all5:
            xs = [R[i] for i in combo]
            e1,e2,e3,e4,e5 = esymm(xs)
            mk = multiset_key(xs)
            sumbuckets.setdefault(key(e1), set()).add(mk)
            b1235.setdefault((key(e1),key(e2),key(e3),key(e5)), set()).add(mk)
            b125.setdefault((key(e1),key(e2),key(e5)), set()).add(mk)
        colA = sum(len(v)-1 for v in sumbuckets.values() if len(v)>1)
        totA = sum(len(v) for v in sumbuckets.values())
        colB = sum(len(v)-1 for v in b1235.values() if len(v)>1)
        colD = sum(len(v)-1 for v in b125.values() if len(v)>1)
        print(f"n={n:3d}  #5-multisets={len(all5):5d}  "
              f"(A)sum-only extra-collisions={colA:5d}/{totA}  "
              f"(B)(e1,e2,e3,e5) extra-coll={colB:5d}  "
              f"(D)(e1,e2,e5) extra-coll={colD:5d}")

    # (C) conjugation identity  e_4 == e_5 * conj(e_1)
    print("== conjugation identity e_4 == e_5 * conj(e_1) (roots of unity) ==")
    maxerr = 0.0
    for n in (5,6,8,10,16,32):
        R = roots(n)
        for _ in range(2000):
            xs = [random.choice(R) for _ in range(5)]
            e1,e2,e3,e4,e5 = esymm(xs)
            lhs = e4
            rhs = e5 * (e1.conjugate())
            maxerr = max(maxerr, abs(lhs-rhs))
        # also alt e_3 == e_5 * conj(e_2)
    print(f"  e_4 == e_5*conj(e_1) maxerr = {maxerr:.2e}  (expect ~1e-12)")
    maxerr2 = 0.0
    for n in (5,6,8,10,16,32):
        R = roots(n)
        for _ in range(2000):
            xs = [random.choice(R) for _ in range(5)]
            e1,e2,e3,e4,e5 = esymm(xs)
            maxerr2 = max(maxerr2, abs(e3 - e5*(e2.conjugate())))
    print(f"  e_3 == e_5*conj(e_2) maxerr = {maxerr2:.2e}  (expect ~1e-12)")

if __name__ == "__main__":
    run()
