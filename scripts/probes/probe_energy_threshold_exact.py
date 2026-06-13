#!/usr/bin/env python3
"""EXACT clean-threshold for the delta* keystone E_{F_p}(mu_n) (#389).

The delta* floor rests on E_{F_p}(mu_n) = 3n(n-1) (clean transfer). The swarm framed
the transfer threshold as "sharp at ~n^2.3"; the energy cross-check (probe_energy_
keystone_verify.py) showed that is prime-specific + non-monotone. THIS probe pins the
EXACT condition: surplus (E > 3n(n-1)) occurs iff some non-char-0-trivial quadruple
(a,b,c,d) in mu_n^4 has a+b=c+d mod p but not in Z[zeta_n], i.e.
        p | N(zeta^i + zeta^j - zeta^k - zeta^l)     (cyclotomic norm).
Hence:  E_{F_p}(mu_n) = 3n(n-1)  <=>  p divides NONE of the quadruple norms.
Norm computed EXACTLY as det of the mult-by-alpha matrix on Z[x]/(x^(n/2)+1)
(fraction-free Bareiss). The "bad primes" form a FINITE explicit set, bounded by
max|norm| = 4^(phi(n)) = 4^(n/2).

CROSS-VALIDATED (triple): bad-prime sets match probe_energy_keystone_verify.py exactly
 - n=8:  bad = {17,41}            -> all p>41 clean (E=168)
 - n=16: bad = {17,41,97,113,193,257,337} -> all p>337 clean; 337 surplus, 449/593 clean
 - n=32: 4129 (quad (0,1,2,6)) and 1153 (quad (0,1,3,12)) confirmed surplus-capable
FORMALIZATION IMPLICATION: the right hypothesis is NORM-COPRIMALITY (p coprime to the
quadruple-norm product), provable; a "p >= n^c" power threshold is both false-as-stated
(non-monotone) and the wrong KIND of condition. Provable sufficient bound: p > 4^(n/2).
"""
# EXACT threshold for the keystone E_{F_p}(mu_n) = 3n(n-1): which primes are "clean"?
# Surplus (E > 3n(n-1)) iff some non-trivial quadruple (a,b,c,d) in mu_n^4 has
# a+b=c+d mod p but NOT in Z[zeta_n], i.e. p | N(zeta^i+zeta^j-zeta^k-zeta^l).
# So: p CLEAN  <=>  p divides NONE of the quadruple cyclotomic norms.
# Norm computed exactly as det of the mult-by-alpha matrix on Z[x]/(x^(n/2)+1).
from itertools import product
from collections import Counter

def det_int(M):
    # exact integer determinant via fraction-free Bareiss
    n = len(M); M = [row[:] for row in M]; sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            piv = next((r for r in range(k+1,n) if M[r][k] != 0), None)
            if piv is None: return 0
            M[k], M[piv] = M[piv], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n-1][n-1]

def reduce_pow(e, h):           # x^e in Z[x]/(x^h+1): returns (sign, exp<h)
    s = 1
    while e >= h: e -= h; s = -s
    return s, e

def alpha_vec(i,j,k,l, h):      # coeff vector of zeta^i+zeta^j-zeta^k-zeta^l, len h
    v = [0]*h
    for (e, c) in ((i,1),(j,1),(k,-1),(l,-1)):
        s, ee = reduce_pow(e % (2*h), h); v[ee] += c*s
    return v

def mult_matrix(v, h):          # mult-by-(sum v_t x^t) on Z[x]/(x^h+1)
    M = [[0]*h for _ in range(h)]
    for col in range(h):        # x^col * v
        for t in range(h):
            if v[t]:
                s, ee = reduce_pow(t+col, h)
                M[ee][col] += s*v[t]
    return M

def norm(i,j,k,l, h):
    return det_int(mult_matrix(alpha_vec(i,j,k,l,h), h))

def prime_factors(x):
    x = abs(x); fs=set(); d=2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs

# n=16 (h=8): exhaustive over non-trivial quadruples, collect all surplus-prime divisors
n=16; h=n//2
surplus_primes=set(); maxnorm=0; cnt=0
for i,j,k,l in product(range(n),repeat=4):
    if {i,j}=={k,l}: continue        # char-0-trivial multiset
    N=norm(i,j,k,l,h)
    if N==0: continue                # extra char-0 relation (rare; antipodal etc.)
    cnt+=1; maxnorm=max(maxnorm,abs(N))
    surplus_primes |= {p for p in prime_factors(N) if p>n}
sp=sorted(surplus_primes)
print(f"n={n}: {cnt} non-trivial quadruples, max|norm|={maxnorm} (~4^{h}={4**h})")
print(f"  surplus-capable primes (p>n dividing some quadruple norm), p<=2000: {[p for p in sp if p<=2000]}")
print(f"  total distinct surplus-capable primes: {len(sp)}, largest {sp[-1] if sp else None}")
# cross-validate against energy-probe surplus primes for n=16: 337 surplus, 593/449 clean
for p in (337, 593, 449, 257):
    print(f"  p={p}: {'SURPLUS-capable (divides a quadruple norm)' if p in surplus_primes else 'CLEAN (divides none)'}")

print()
# n=8 (h=4): fast exhaustive
n=8; h=4; sp=set(); mx=0
for i,j,k,l in product(range(n),repeat=4):
    if {i,j}=={k,l}: continue
    N=norm(i,j,k,l,h)
    if N==0: continue
    mx=max(mx,abs(N)); sp|={p for p in prime_factors(N) if p>n}
print(f"n=8: max|norm|={mx} (4^{h}={4**h}); surplus-capable primes: {sorted(sp)}")
print(f"  ⟹ ALL p>{max(sp) if sp else 0} (p≡1 mod 8) are CLEAN: E=3n(n-1)=168 exactly")

# n=32 (h=16): targeted — confirm energy-probe surplus primes 4129, 1153 divide some norm
n=32; h=16
def divides_some_norm(p, n, h, budget=400000):
    cnt=0
    for i,j,k,l in product(range(n),repeat=4):
        if {i,j}=={k,l}: continue
        if norm(i,j,k,l,h) % p == 0: return (i,j,k,l)
        cnt+=1
        if cnt>=budget: return None
    return None
for p in (4129, 1153):
    w = divides_some_norm(p, n, h)
    print(f"n=32 p={p}: {'surplus-capable, e.g. quadruple '+str(w) if w else 'no norm divisor found in budget'}")
