#!/usr/bin/env python3
"""Exact char-0 probe: t-fiber exhaustiveness on mu_n (n=2^m) via the squaring tower.

CONJECTURE under test (O47 crystallized; proof sketch = Newton + antipodal descent):
  {S in C(mu_n, w) : e_1(S)=...=e_t(S)=0}  =  { s^{-L}(U) : U subset mu_{n/2^L} },
  L = floor(log2 t) + 1, count = C(n/2^L, w/2^L) if 2^L | w else 0.

Arithmetic: Z[x]/(x^{n/2}+1), zeta = x. Exact integers, no floats.
e_j checked DIRECTLY via prod (T - zeta^i) coefficients (not via Newton),
so the probe is independent of the Newton step of the proof.
"""
import itertools, math, sys

def mulmod(a, b, half):
    # multiply two coeff lists mod x^half + 1
    out = [0]*half
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj == 0: continue
            k = i + j
            if k < half: out[k] += ai*bj
            else: out[k - half] -= ai*bj
    return out

def run(m, tmax, verbose=True):
    n = 2**m; half = n//2
    zeta_pow = []  # zeta^i as coeff list, i < n
    for i in range(n):
        c = [0]*half
        if i < half: c[i] = 1
        else: c[i-half] = -1
        zeta_pow.append(c)
    fails = 0
    for w in range(1, n+1):
        # enumerate subsets of size w; compute e_1..e_tmax via elementary symmetric recurrence
        fiber_counts = {t: 0 for t in range(1, tmax+1)}
        members = {t: [] for t in range(1, tmax+1)}
        for S in itertools.combinations(range(n), w):
            # e_j recurrence: prod (1 + y*zeta^i) coefficients in y, up to degree tmax
            e = [[0]*half for _ in range(tmax+1)]  # e[0] = 1
            e0 = [0]*half; e0[0] = 1; e = [e0] + [[0]*half for _ in range(tmax)]
            for i in S:
                zi = zeta_pow[i]
                for j in range(min(tmax, w), 0, -1):
                    add = mulmod(e[j-1], zi, half)
                    e[j] = [a+b for a, b in zip(e[j], add)]
            for t in range(1, tmax+1):
                if t > w: continue
                if all(all(c == 0 for c in e[j]) for j in range(1, t+1)):
                    fiber_counts[t] += 1
                    members[t].append(S)
        for t in range(1, min(tmax, n)+1):
            L = t.bit_length()  # floor(log2 t) + 1
            if 2**L > n:
                pred = 1 if w == n else 0  # degenerate: only full domain? skip
                continue
            nd, = [n // 2**L]
            pred = math.comb(nd, w // 2**L) if w % 2**L == 0 else 0
            got = fiber_counts[t]
            status = "OK " if got == pred else "FAIL"
            if got != pred:
                fails += 1
                print(f"  {status} n={n} w={w} t={t}: got {got} predicted {pred}")
                for S in members[t][:4]: print("      ", S)
            elif verbose and got > 0:
                print(f"  {status} n={n} w={w} t={t}: {got} = C({nd},{w//2**L})")
        # structural check at one (w,t): members are unions of 2^L-cosets (i mod n/2^L classes)
    return fails

total = 0
for m, tmax in [(3, 4), (4, 6)]:
    print(f"=== n = 2^{m} = {2**m}, t up to {tmax} ===")
    total += run(m, tmax)
print("RESULT:", "ALL PASS" if total == 0 else f"{total} FAILURES")
