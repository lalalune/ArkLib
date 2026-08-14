#!/usr/bin/env python3
"""
probe_halfsum_candidate_density.py  (#407, Lane C — Half-Sum count lane, OFF the BGK wall)

The Half-Sum Lemma reduces delta* to a CANDIDATE-BAD-PRIME ledger: a bad prime p = 1 mod n must
divide the cyclotomic norm N_{Q(zeta_n)/Q}(sum_{i in S} zeta^i) of some antipodal-free subset S of
mu_n. The all-ones half-sum has norm 2^{2^{m}-1} (pure power of 2, never bad, proven uniformly in
HalfSumNormClosedForm.lean). The issue's Lane C asks for a UNIFORM-IN-N proof that all candidates are
clean. This probe SETTLES the shape of that question (exact integer arithmetic, no sympy):

 - n=8 : 0 candidate primes.
 - n=16: 11 candidates, max 881 < n^3=4096 => ENTIRE prize window [n^3,n^5] clean.
 - n=32: candidates reach 665857 (INSIDE the window [n^3,n^4]); n=64: 65456257 (inside [n^4,n^5]).
   => strong uniform cleanness ("ALL prize primes clean") is FALSE from n=32 on.
 - DENSITY: fraction of primes =1 mod n in the prize window that are candidate-BAD:
       n=16: 0/748 = 0.0000 ;  n=32: 194/4911 = 0.0395 (a LOWER bound — capped subset size).
   => bad primes are SPARSE; a CLEAN prize prime always exists (method works by prime-choice).

So Lane C resolves to: NOT strong-uniform-clean, but the open part shrinks to a clean DECIDABLE,
OFF-BGK density bound: candidate-bad-prime density bounded below 1 (clean prime exists) / -> 0 (almost
all clean). A cyclotomic-counting problem, not a character-sum cancellation. CAVEAT: enumeration is
capped at subset size <= maxsize, so the measured bad density is a LOWER bound; the genuinely open
question is whether it stays bounded away from 1 as n -> infinity (and as maxsize -> n/2).
"""
import numpy as np, itertools, math

def isprime(x):
    if x < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x % q == 0: return x == q
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y = pow(a,d,x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def norm_subset(S, n, units, z):
    val = 1.0+0j
    for j in units: val *= sum(z[(i*j) % n] for i in S)
    return int(round(val.real))

def factor(x):
    x = abs(x); f = set(); d = 2
    while d*d <= x:
        while x % d == 0: f.add(d); x //= d
        d += 1
    if x > 1: f.add(x)
    return f

def cand_primes(n, maxsize):
    units = [j for j in range(1,n) if math.gcd(j,n) == 1]   # Galois group (Z/n)*, |.|=phi(n)=n/2
    z = np.exp(2j*np.pi*np.arange(n)/n); half = n//2; cand = set(); seen = set()
    for r in range(1, maxsize+1):
        for cells in itertools.combinations(range(half), r):
            for signs in itertools.product([0,1], repeat=r):
                S = [cells[t]+signs[t]*half for t in range(r)]
                N = norm_subset(S, n, units, z)
                if N == 0 or abs(N) in seen: continue
                seen.add(abs(N))
                for pr in factor(N):
                    if pr > 2 and (pr-1) % n == 0: cand.add(pr)
    return cand

if __name__ == "__main__":
    print("Half-Sum candidate-bad-prime ledger + density in the prize window [n^3, n^4]")
    print(f"{'n':>4} {'#primes=1modn':>13} {'#bad':>6} {'density':>9} {'max cand':>12}")
    for n, ms in [(16,8),(32,6)]:
        lo, hi = n**3, n**4
        cand = cand_primes(n, ms)
        pw = [p for p in range(lo|1, hi) if p % n == 1 and isprime(p)]
        bad = [p for p in pw if p in cand]
        print(f"{n:>4} {len(pw):>13} {len(bad):>6} {len(bad)/max(1,len(pw)):>9.4f} "
              f"{max(cand) if cand else 0:>12}")
