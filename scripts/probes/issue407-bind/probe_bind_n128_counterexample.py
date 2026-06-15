#!/usr/bin/env python3
"""Confirm the (BIND) counterexample mechanism at n=128 with a thin prize-scale prime.
Find a non-antipodal S subset {0..127} (binding-ish size) with Sum_{i in S} omega^i == 0 mod p,
p a thin prime (p>n^3, n|p-1), beta=log_n p >= 4. Direct F_p search via linear algebra:
the n powers {omega^i} in F_p span F_p (1-dim), so a {0,1}-combination summing to 0 is a 0/1 null
vector. We want a SPARSE-ish non-antipodal one. Easiest: pick p, build omega, then find any non-antipodal
0/1 vector summing to 0 by greedy/meet-in-middle on a subset of indices.
"""
from sympy import isprime, primitive_root, primefactors
import math, random
n = 128
m = n // 2

def find_p(beta_min=4.0, beta_max=4.6):
    lo = int(n**beta_min); hi = int(n**beta_max)
    mlo = lo // n
    cand = []
    mm = mlo
    while len(cand) < 1 and mm*n+1 < hi:
        p = mm*n + 1
        if isprime(p):
            cand.append(p)
        mm += 1
    return cand[0] if cand else None

p = find_p()
print(f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} thin(p>n^3={n**3}): {p>n**3}", flush=True)
g = primitive_root(p); w = pow(g, (p-1)//n, p)
assert pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in primefactors(n))
vals = [pow(w, i, p) for i in range(n)]  # the n residues

# meet-in-the-middle to find a non-antipodal 0/1 vanisher.
# split indices into two halves; want subset A of first half + subset B of second half, sum==0 mod p, non-antipodal.
random.seed(5)
H1 = list(range(0, m)); H2 = list(range(m, n))
# limit subset size to keep MITM tractable: choose random subsets, hash partial sums
from collections import defaultdict
table = defaultdict(list)
# enumerate moderate subsets of H1 (sizes up to ~12) by random sampling
for _ in range(300000):
    k = random.randint(1, 12)
    A = random.sample(H1, k)
    s = sum(vals[i] for i in A) % p
    table[s].append(tuple(A))
    if len(table) > 600000:
        break
found = None
for _ in range(300000):
    k = random.randint(1, 12)
    B = random.sample(H2, k)
    s = sum(vals[i] for i in B) % p
    need = (-s) % p
    if need in table:
        for A in table[need]:
            S = list(A) + list(B)
            Ss = set(S)
            if len(Ss) != len(S):
                continue
            antipodal = all(((i+m) % n) in Ss for i in S)
            if not antipodal:
                # verify
                if sum(vals[i] for i in S) % p == 0:
                    found = sorted(S)
                    break
    if found:
        break

if found:
    Ss = set(found)
    anti = all(((i+m) % n) in Ss for i in found)
    val = sum(vals[i] for i in found) % p
    print(f"FOUND non-antipodal vanisher at n=128: #S={len(found)}", flush=True)
    print(f"  non-antipodal: {not anti};  Sum w^i mod p = {val} (==0: {val==0})", flush=True)
    print(f"  house (#S)^phi = {len(found)}^{m} ~ 2^{m*math.log2(len(found)):.0f}  vs p~2^{math.log2(p):.0f} (house>>p => gate hyp FALSE)", flush=True)
    print(f"  S={found}", flush=True)
    print(f"  >>> (BIND) COUNTEREXAMPLE at n=128, p={p}", flush=True)
else:
    print("no non-antipodal vanisher found in sampled budget (mechanism not exhibited at n=128 here)", flush=True)
