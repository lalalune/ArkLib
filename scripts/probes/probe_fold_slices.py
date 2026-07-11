#!/usr/bin/env python3
"""Corrected: branch path of exponent e = ceil-half digit code:
c_k = e_{k-1} mod 2; e_k = (e_{k-1} + c_k)/2  (even fold: e->e/2; odd fold: e->(e+1)/2 due to the y-twist).
Claim: branch (c1..cl) alive <-> some coeff exponent e has ceil-half digits (c1..cl);
and that digit code depends only on e mod 2^l (so branches = residue classes mod 2^l, repermuted).
"""
import random
random.seed(7)
p = 97; n = 16
g = None
for cand in range(2, p):
    if pow(cand, n, p) == 1 and all(pow(cand, n//q, p) != 1 for q in [2]):
        g = cand; break
mu = [pow(g, i, p) for i in range(n)]

def branch_tree(S, v, depth):
    levels = [[dict(v)]]
    for l in range(depth):
        nxt = []
        for vb in levels[-1]:
            fe = {}; fo = {}
            for y in sorted(set(pow(x, 2, p) for x in vb)):
                fib = [x for x in vb if pow(x, 2, p) == y]
                e = sum(vb[x] for x in fib) % p
                o = sum(vb[x]*x for x in fib) % p
                if e: fe[y] = e
                if o: fo[y] = o
            nxt.append(fe); nxt.append(fo)
        levels.append(nxt)
    return levels

def ceilhalf_digits(e, l):
    ds = []
    for _ in range(l):
        c = e % 2
        ds.append(c)
        e = (e + c) // 2
    return tuple(ds)

FAILS = 0; CLASSCHECK = 0
# sanity: digit code constant on residue classes mod 2^l
for l in range(1, 5):
    for b in range(2**l):
        codes = {ceilhalf_digits(b + k*2**l, l) for k in range(4)}
        if len(codes) != 1: CLASSCHECK += 1

for trial in range(500):
    D = random.randint(1, n-2)
    coeffs = {}
    for _ in range(random.randint(1, 7)):
        coeffs[random.randint(0, D)] = random.randint(1, p-1)
    v = {x: sum(c*pow(x, ee, p) for ee, c in coeffs.items()) % p for x in mu}
    v = {x: val for x, val in v.items() if val != 0}
    if not v: continue
    depth = 3
    tree = branch_tree({x: v[x] for x in v}, v, depth)
    for l in range(1, depth+1):
        alive_tree = [len(d) > 0 for d in tree[l]]
        # tree index i: bits c1..cl with c1 = MSB of expansion order (first fold)
        want = []
        for i in range(2**l):
            bits = tuple((i >> (l-1-k)) & 1 for k in range(l))
            alive = any(ceilhalf_digits(ee, l) == bits for ee, c in coeffs.items() if c % p != 0)
            want.append(alive)
        if alive_tree != want:
            FAILS += 1
            if FAILS <= 3:
                print(f"MISMATCH trial={trial} l={l} coeffs={coeffs}\n  tree:{alive_tree}\n  want:{want}")
print("class-constancy violations:", CLASSCHECK)
print("RESULT:", "ALL MATCH (500 trials, depths 1-3)" if FAILS == 0 else f"{FAILS} mismatches")
