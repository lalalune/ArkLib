#!/usr/bin/env python3
"""
E12 three-gap positional rigidity probe (#444, prize regime).

OBJECT: mu_n = <g^((p-1)/n)> the THIN 2-power subgroup of F_p*, n=2^a.
The "orbit positions" are the residues {x : x in mu_n} viewed in [0,p) (additive line),
OR the angular positions arg(e_p(bx)) = 2pi*bx/p on the circle for the worst frequency b.

THREE-DISTANCE THEOREM (Steinhaus): the points {k*alpha mod 1 : k=0..N-1} partition the
circle into gaps taking AT MOST 3 distinct lengths. E12 asks: do the mu_n positions (which
are NOT k*alpha but a multiplicative subgroup) inherit a bounded-distinct-gap rigidity?

We test, in the PRIZE REGIME (PROPER subgroup, p>>n^3, p=1 mod n, NEVER n=q-1):
  (A) GAPS of the sorted additive positions of mu_n in [0,p): how many DISTINCT gap lengths?
      (mu_n is a subgroup, NOT an arithmetic progression, so we do NOT expect <=3 trivially.)
  (B) The KEY E12 claim: at the WORST frequency b (maximizing |eta_b|), the sorted angular
      positions {b*x mod p : x in mu_n} -- do THEY have bounded distinct gaps? And is the
      worst b precisely one whose orbit positions are MAXIMALLY rigid (few gaps)?
  (C) Correlation: is |eta_b| LARGE exactly when the #distinct-gaps of {b*x mod p} is SMALL?
      (positional rigidity <=> large character sum, the E12 mechanism)
"""
import cmath, math

def primitive_root(p):
    # find a generator of F_p*
    fac = []
    m = p-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of order-n subgroup
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = x*h % p
    return sorted(S)

def eta(p, b, mu):
    return sum(cmath.exp(2j*math.pi*b*x/p) for x in mu)

def distinct_gaps(positions, p):
    # sorted positions on the cyclic group Z_p; gap lengths (cyclic)
    s = sorted(positions)
    gaps = []
    for i in range(len(s)):
        nxt = s[(i+1) % len(s)]
        d = (nxt - s[i]) % p
        gaps.append(d)
    # round to handle nothing (integers, exact)
    return len(set(gaps)), sorted(set(gaps))

def find_primes(n, count, minratio=3):
    # p == 1 mod n, p > n^minratio, prime
    res = []
    lo = max(n**minratio, n+1)
    cand = lo + ((1 - lo) % n)  # smallest >= lo with p==1 mod n
    if cand <= lo: cand += n
    while len(res) < count:
        if cand > 1 and is_prime(cand):
            res.append(cand)
        cand += n
    return res

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

print("E12 three-gap positional rigidity -- PRIZE REGIME (proper mu_n, p>>n^3, p=1 mod n)")
print("="*78)
for a in range(2, 7):
    n = 2**a
    primes = find_primes(n, 2, minratio=3)
    for p in primes:
        mu = subgroup(p, n)
        assert len(mu) == n and len(mu) < p-1, "must be PROPER subgroup"
        # (A) additive positions of mu_n itself
        ndg_add, _ = distinct_gaps(mu, p)
        # (B/C) over all frequencies b != 0: |eta_b| and #distinct gaps of {b*x mod p}
        best_b, best_mag = None, -1
        rows = []
        for b in range(1, min(p, 400)):
            orbit = [(b*x) % p for x in mu]
            ndg, _ = distinct_gaps(orbit, p)
            mag = abs(eta(p, b, mu))
            rows.append((b, mag, ndg))
            if mag > best_mag:
                best_mag, best_b = mag, b
        # correlation: among top-5 |eta_b|, what's the mean #distinct-gaps vs overall mean?
        rows.sort(key=lambda r: -r[1])
        top = rows[:5]
        bot = rows[-5:]
        mean_top_ndg = sum(r[2] for r in top)/len(top)
        mean_all_ndg = sum(r[2] for r in rows)/len(rows)
        # worst orbit distinct gaps
        worst_ndg = next(r[2] for r in rows if r[0]==best_b)
        sqrt_bound = math.sqrt(n)
        print(f"n={n:4d} p={p:8d}  M={best_mag:7.3f} (sqrt n={sqrt_bound:6.3f}, ratio {best_mag/sqrt_bound:.2f})")
        print(f"        add-positions #distinct-gaps={ndg_add} (n={n})  | worst-b={best_b} orbit #gaps={worst_ndg}")
        print(f"        mean #gaps top5-|eta|={mean_top_ndg:.1f}  vs all-mean={mean_all_ndg:.1f}  (rigidity if top<all)")
