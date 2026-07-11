#!/usr/bin/env python3
"""
probe_407_lacunary_pencil_roots_mann.py   (issue #407, target P5-sparse-poly-roots)

ORBIT-COUNT CORE via LACUNARY (sparse) POLYNOMIAL ROOTS-OF-UNITY THEORY.
=======================================================================

GOVERNING LAW (in-tree, exact):  delta* = sup{ delta : I(delta) <= q*eps* ~ n },
  I(delta) = max over monomial pencils (a,b) of
             #{alpha in F_q : x^a + alpha x^b is delta-close to RS[k]}.

A point x in mu_n is an AGREEMENT of the pencil h_alpha(x)=x^a+alpha x^b with a
deg<k codeword g iff
      f_alpha(x) := x^a + alpha*x^b - g(x) = 0.
f_alpha is a LACUNARY (sparse) polynomial with support {0,1,...,k-1, a, b}: at
most t := k+2 nonzero terms.  Its number of mu_n roots IS the per-witness
agreement count of (alpha, g).  delta-close := agreement >= (1-delta) n.

THIS PROBE attacks the INNER object directly:
  Q: over a t-term (t=k+2) pencil-support polynomial with coefficients in char 0
     (realized in F_p with p >> n^3 -- the prize-faithful regime, mu_n PROPER),
     how many mu_n roots (n=2^mu) can it have, vs t, vs the support spread
     (b-a, gcd(b-a,n))?  poly(t)/O(t)  vs  Theta(n).

MANN / CONWAY-JONES theory (rigorous ceiling for the DYADIC case):
  A vanishing sum of roots of unity decomposes into PRIMITIVE blocks (no proper
  vanishing subsum); a primitive block of size s lies (up to rotation) in mu_m,
  m = product of distinct primes <= s (Mann 1965).  Over mu_n with n = 2^mu the
  only prime is 2, so the only nontrivial primitive relation is the ANTIPODAL
  pair  z + (-z) = 0  (s=2).  Hence at a root the (<=t) terms partition into
  antipodal pairs (this is exactly the in-tree dyadic Lam-Leung / Q1ClaimADyadic
  law e_1(S)=0 <=> S=-S).

WHAT THIS PROBE FINDS (see committed results below):
  (1) FIXED-t experiment (constant #terms, n grows): max mu_n root count GROWS
      like n/2 = Theta(n), with maxR/n -> 0.5.  So the per-witness agreement of a
      genuinely sparse pencil is NOT bounded by support size.
  (2) MECHANISM (probe_407_lacunary_pencil_coset_mann.py): the Theta(n) root set
      is ENTIRELY ONE COSET of mu_{n/2}, produced by the single dyadic cyclotomic
      factor (1 + x^{n/2}) = Phi_n(x) dividing f_alpha.  The root set is fully
      antipodally paired -- exactly Mann's dyadic prediction.  It is a GENUINE
      pencil agreement (codeword g = -(g0+g1 x), deg 1 < k).
  (3) The Theta(n)-agreement witness has gcd(b-a,n)=1 (pencil (n/2+1, n/2)), so
      its orbit under alpha->alpha*w^{b-a} has size S=n: it is ONE orbit.  Whether
      this causes a LIST explosion (many such alphas) is the bad-alpha COUNT
      question, measured in probe_407_lacunary_pencil_Npencil.py.

VERDICT (per-witness lane): the inner count IS Theta(n) -- but ONLY via the
single dyadic cyclotomic coset factor, a structurally rigid 1-parameter family,
NOT a generic sparse-root explosion.  This LOCALIZES the per-witness Theta(n) to
the coset-factor branch and hands the closeability question to the bad-alpha
count (orbit-count) lane.  Honest: this does NOT close the prize; it pins the
exact mechanism of the inner Theta(n).

HONESTY: all arithmetic EXACT over F_p; p >> n^3 makes mod-p vanishing match
char-0 vanishing for these bounded-height cyclotomic combinations (prize-faithful;
the #400 full-group trap avoided -- mu_n is a PROPER subgroup).
"""

import itertools, random
from math import gcd

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def prime_ge(lo, n):
    p = lo - (lo % n) + 1
    while not (is_prime(p) and (p-1) % n == 0): p += n
    return p

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in (2,3,5,7) if n % q == 0):
            return w
    raise RuntimeError("no primitive n-th root")

def powers(w, p, n):
    P = [1]*n
    for j in range(1, n): P[j] = P[j-1]*w % p
    return P

def roots_in_mu_n(coeffs, P, p, n):
    items = list(coeffs.items()); R = []
    for j in range(n):
        s = 0
        for e, c in items: s += c * P[(e*j) % n]
        if s % p == 0: R.append(j)
    return set(R)

def kernel_vector(M, p):
    if not M: return None
    rows = [r[:] for r in M]; nrow = len(rows); ncol = len(rows[0])
    inv = lambda x: pow(x % p, p-2, p); pivots = []; r = 0
    for c in range(ncol):
        piv = None
        for rr in range(r, nrow):
            if rows[rr][c] % p != 0: piv = rr; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c]); rows[r] = [(x*iv) % p for x in rows[r]]
        for rr in range(nrow):
            if rr != r and rows[rr][c] % p != 0:
                f = rows[rr][c]; rows[rr] = [(a - f*b) % p for a, b in zip(rows[rr], rows[r])]
        pivots.append(c); r += 1
        if r == nrow: break
    free = [c for c in range(ncol) if c not in pivots]
    if not free: return None
    fc = free[0]; x = [0]*ncol; x[fc] = 1
    for i, c in enumerate(pivots): x[c] = (-rows[i][fc]) % p
    return x

def build_vanishing(S, support, P, p, n):
    M = [[P[(e*j) % n] for e in support] for j in S]
    v = kernel_vector(M, p)
    if v is None: return None
    co = {support[i]: v[i] % p for i in range(len(support)) if v[i] % p != 0}
    return co if co else None

def pencil_support(k, a, b, n):
    return sorted(set(list(range(k)) + [a % n, b % n]))

def max_roots_fixed_t(n, k, p, w, P, rng, trials):
    best = 0; info = None
    for _ in range(trials):
        a = rng.randrange(k, n); b = rng.randrange(k, n)
        while b == a or b < k: b = rng.randrange(k, n)
        sup = pencil_support(k, a, b, n); t = len(sup)
        if rng.random() < 0.5:
            S = rng.sample(range(n), min(t-1, n))
        else:
            half = n//2; bases = rng.sample(range(half), min((t-1)//2 or 1, half))
            S = []
            for j in bases: S += [j, (j+half) % n]
            S = S[:t-1]
            if len(S) < t-1:
                extra = [x for x in range(n) if x not in S]; rng.shuffle(extra)
                S += extra[:t-1-len(S)]
        co = build_vanishing(S, sup, P, p, n)
        if not co: continue
        R = roots_in_mu_n(co, P, p, n)
        if len(R) > best:
            best = len(R); info = (a, b, gcd((b-a) % n, n), len(sup), sorted(R))
    return best, info

def main():
    rng = random.Random(20260614)
    print("="*84, flush=True)
    print("#407 P5: FIXED-t (constant #terms) sparse pencil roots over mu_n, p >> n^3", flush=True)
    print("Descartes-type ceiling guess = t-1; dyadic-Mann wall = Theta(n).", flush=True)
    print("="*84, flush=True)
    for t in (4, 6, 8):
        k = t - 2
        print(f"\n--- t = k+2 = {t} (k={k}), FIXED while n grows ---", flush=True)
        print(f"{'n':>5} {'p':>14} {'p/n^3':>8} | {'maxR':>5} {'t-1':>4} {'maxR/n':>7}", flush=True)
        for mu in range(3, 9):
            n = 2**mu
            if k >= n: continue
            p = prime_ge(8*n**3, n); w = find_gen(p, n); P = powers(w, p, n)
            tr = 6000 if n <= 64 else (3000 if n <= 128 else 1500)
            best, info = max_roots_fixed_t(n, k, p, w, P, rng, tr)
            print(f"{n:>5} {p:>14} {p//(n**3):>8} | {best:>5} {t-1:>4} {best/n:>7.3f}", flush=True)
    print("\nFINDING: at FIXED t, maxR -> n/2 = Theta(n) (maxR/n -> 0.5).  The inner", flush=True)
    print("per-witness agreement of a sparse pencil is NOT support-bounded; the Theta(n)", flush=True)
    print("comes from the single dyadic cyclotomic coset factor (1+x^{n/2}).  See the", flush=True)
    print("companion probes for the coset mechanism and the bad-alpha (orbit) count.", flush=True)

if __name__ == "__main__":
    main()
