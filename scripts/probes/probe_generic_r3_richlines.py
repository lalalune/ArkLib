#!/usr/bin/env python3
"""#389 DECISIVE generic-regime test for r=3, m=1.

For s = 8 the KKH26 generic threshold is s^(s/2) = 8^4 = 4096, so p = 12289 and
p = 65537 are BOTH GENERIC (p > s^(s/2)) -- the regime where N_fib should be the
field-correct fibre value (no small-integer collisions). This is the regime my earlier
probes (p=17,41,97 all sub-generic) could NOT reach.

Question: is N_fib(8,3) = C(3,1) = 3 the MAXIMUM number of 3-rich lines over ALL words
w: mu_8 -> F_p, or do HIGHER-DEGREE words beat it? (Low-degree words give conics, <=2-rich;
the cubic gives the zero-sum fibre = 3; degree >=4 words are the open question.)

If max = 3, strong evidence N_fib is the exact answer at r=3.
If a word beats 3, the conjecture max = N_fib is REFUTED and the true answer is larger.
"""
import itertools, random, sys
from collections import Counter
from math import comb

random.seed(389)


def subgroup(p, s):
    for h in range(2, p):
        g = pow(h, (p - 1) // s, p)
        o, x = 1, g
        while x != 1:
            x = x * g % p; o += 1
        if o == s:
            return [pow(g, i, p) for i in range(s)]
    raise RuntimeError("no subgroup")


def num_rich_lines(mus, w, p, a):
    """#lines y=cx+d agreeing with w on >= a domain points (k=2: degree-1 codewords).
    Build line -> set of x via point pairs (each pair determines a unique line)."""
    n = len(mus)
    pts = [(mus[i], w[i]) for i in range(n)]
    line_pts = {}
    for i in range(n):
        xi, yi = pts[i]
        for j in range(i + 1, n):
            xj, yj = pts[j]
            c = (yj - yi) * pow((xj - xi) % p, p - 2, p) % p
            d = (yi - c * xi) % p
            line_pts.setdefault((c, d), set()).update([i, j])
    return sum(1 for sset in line_pts.values() if len(sset) >= a)


def run(p, s, a, nfib):
    mus = subgroup(p, s)
    n = len(mus)
    print(f"\n=== p={p}  s={s}  n={n}  a={a}  N_fib={nfib}  "
          f"(generic: p>{s}^{s//2}={s**(s//2)}: {p > s**(s//2)}) ===")
    results = {}
    # monomials x^d for all d
    for d in range(1, s):
        w = [pow(x, d, p) for x in mus]
        results[f"x^{d}"] = num_rich_lines(mus, w, p, a)
    # ladder x^3 + lam x^2 over all lam (the fibre family)
    best_lad = 0
    for lam in range(p):
        w = [(pow(x, 3, p) + lam * pow(x, 2, p)) % p for x in mus]
        best_lad = max(best_lad, num_rich_lines(mus, w, p, a))
    results["ladder x^3+lam x^2"] = best_lad
    # general cubic a x^3 + b x^2 + c x + e (translation/scaling) - sample
    best_cub = 0
    for _ in range(3000):
        A = random.randrange(1, p); B = random.randrange(p)
        C = random.randrange(p); E = random.randrange(p)
        w = [(A*pow(x,3,p)+B*pow(x,2,p)+C*x+E) % p for x in mus]
        best_cub = max(best_cub, num_rich_lines(mus, w, p, a))
    results["cubic(sampled)"] = best_cub
    # higher-degree polynomial words (the open question)
    best_hi = 0
    for _ in range(3000):
        deg = random.randrange(4, s)
        coeffs = [random.randrange(p) for _ in range(deg+1)]
        w = [sum(coeffs[k]*pow(x,k,p) for k in range(deg+1)) % p for x in mus]
        best_hi = max(best_hi, num_rich_lines(mus, w, p, a))
    results["higher-deg poly(sampled)"] = best_hi
    # arbitrary words: exhaustive is p^n (too big); aggressive hill-climb
    best_climb = 0
    for _ in range(200):
        w = [random.randrange(p) for _ in range(n)]
        cur = num_rich_lines(mus, w, p, a)
        for _st in range(120):
            idx = random.randrange(n); old = w[idx]
            w[idx] = random.randrange(p)
            nv = num_rich_lines(mus, w, p, a)
            if nv >= cur: cur = nv
            else: w[idx] = old
        best_climb = max(best_climb, cur)
    results["hill-climb"] = best_climb
    mx = max(results.values())
    for k, v in sorted(results.items(), key=lambda kv: -kv[1]):
        flag = "  <-- BEATS N_fib!" if v > nfib else ""
        print(f"   {k:30s} {v}{flag}")
    verdict = ("MAX = N_fib (conjecture SURVIVES)" if mx == nfib
               else f"MAX = {mx} > N_fib={nfib} (conjecture REFUTED: answer is larger)"
               if mx > nfib else f"MAX = {mx} < N_fib (shouldn't happen)")
    print(f"   VERDICT: {verdict}")
    return mx, nfib


# r=3, m=1: code degree (r-2)*m = 1 (lines), agreement r*m = 3. k=2.
# N_fib(2^mu, 3) = C(2^(mu-1)-1, 1) = 2^(mu-1)-1.
print("="*70)
print("r=3, m=1: 3-rich lines of the graph of w over mu_s. N_fib = 2^(mu-1)-1.")
for p in [12289, 65537]:
    run(p, 8, 3, 2**(3-1) - 1)    # mu=3, s=8: N_fib = 3
print("="*70)
# also mu=4, s=16: s^(s/2)=16^8 huge, so 12289/65537 are SUB-generic for s=16.
# Report it but flag sub-generic.
for p in [12289, 65537]:
    if (p-1) % 16 == 0:
        run(p, 16, 3, 2**(4-1) - 1)   # mu=4: N_fib(16,3)=7 (SUB-generic, expect inflation)
print("="*70)
print("KEY ROW: s=8 at p=12289/65537 are GENERIC. Their verdict is decisive.")
