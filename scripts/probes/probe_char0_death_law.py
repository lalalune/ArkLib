#!/usr/bin/env python3
"""Item 11 (char-0 face): the field-independent floor of the constrained census.
Z0(n, a, c) = #{a-subsets A of mu_n (n = 2^m) : e_2(A) = ... = e_{c+1}(A) = 0 in char 0},
computed exactly in Z[zeta] by folding. The death point of the char-0 layer is the
field-independent floor of the family death radius c*(n)."""
import sys
from itertools import combinations

def elem_sym_folded(m, A, kmax):
    """folded coefficient vectors of e_2..e_kmax of {g^i : i in A}; early-exit on nonzero."""
    n = 1 << m; N = n >> 1
    # dp over elementary symmetric in Z[zeta]: e_j as dict idx->coeff via folding
    # represent each as length-N int list; multiply by (1 + t*g^x) incrementally:
    # e_j^{new} = e_j + g^x * e_{j-1}
    es = [None]*(kmax+1)
    es[0] = [0]*N; es[0][0] = 1
    for j in range(1, kmax+1): es[j] = [0]*N
    for x in A:
        idx0 = x % n
        for j in range(min(kmax, 1)+0, 0, -1): pass
        for j in range(kmax, 0, -1):
            prev = es[j-1]
            cur = es[j]
            # add g^x * prev
            for t in range(N):
                cv = prev[t]
                if cv:
                    tt = t + idx0
                    if (tt % n) < N: cur[tt % n] = cur[tt % n] + cv if (tt % n) < N else cur
            # redo properly below
    return None

def efold(m, A, jmax):
    n = 1 << m; N = n >> 1
    es = [[0]*N for _ in range(jmax+1)]
    es[0][0] = 1
    for x in A:
        for j in range(jmax, 0, -1):
            prev = es[j-1]; cur = es[j]
            for t in range(N):
                cv = prev[t]
                if cv:
                    tt = (t + x) % n
                    if tt < N: cur[tt] += cv
                    else: cur[tt - N] -= cv
    return es

def census(m, a, c):
    """count a-subsets with e_2 = ... = e_{c+1} = 0 (c constraints)."""
    n = 1 << m
    jmax = c + 1
    cnt = 0; ex = []
    for A in combinations(range(n), a):
        es = efold(m, A, jmax)
        if all(not any(es[j]) for j in range(2, jmax+1)):
            cnt += 1
            if len(ex) < 2: ex.append(A)
    return cnt, ex

print("n=16 char-0 constrained census:", flush=True)
for a in (6, 7, 8, 9, 10):
    for c in (1, 2):
        if a - 4 < c: continue
        cnt, ex = census(4, a, c)
        print(f"  a={a} c={c} (e2..e{c+1}=0): Z0 = {cnt}  {ex[:1]}", flush=True)
print("n=8:", flush=True)
for a in (5, 6):
    cnt, ex = census(3, a, 1)
    print(f"  a={a} c=1: Z0 = {cnt}  {ex[:1]}", flush=True)
print("n=32 (a<=8):", flush=True)
for a in (6, 7, 8):
    for c in (1, 2):
        cnt, ex = census(5, a, c)
        print(f"  a={a} c={c}: Z0 = {cnt}  {ex[:1]}", flush=True)

print("RECURSION TEST (c=3, e2=e3=e4=0):", flush=True)
for (m, a) in ((4, 8), (5, 8), (4, 9)):
    cnt, ex = census(m, a, 3)
    print(f"  n={1<<m} a={a} c=3: Z0 = {cnt}  {ex[:2]}", flush=True)

print("SUBGROUP-COSET SURVIVAL + DEEP DEATH (n=16):", flush=True)
for c in (4, 5, 6):
    cnt, ex = census(4, 8, c)
    print(f"  n=16 a=8 c={c}: Z0 = {cnt}", flush=True)
for c in (1, 2, 3, 4):
    cnt, ex = census(4, 12, c)
    print(f"  n=16 a=12 c={c}: Z0 = {cnt}  {ex[:1]}", flush=True)
