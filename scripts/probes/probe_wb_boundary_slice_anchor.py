#!/usr/bin/env python3
"""Boundary-slice reach of the window pencil law (#371).

The landed count theorem (WBPencilWindowLaw.badScalars_card_le_of_anchor) has no
below-UDR hypothesis: the row-selection J need not be injective, so at the
BOUNDARY SLICE n = 2w+k (the first radius past unique decoding, where the F17
explosion band lives) a duplicated-row selection still anchors the argument.
Anchored <=> pencil corank over F(gamma) is exactly 1 (above the boundary the
column excess forces corank >= 2 and anchors die).

This probe, at boundary instances (17,8,4,w=2) [the C84/F17 exact-value shape]
and (37,12,8,w=2) [q-1 > n+4, robust to the n=q-1 blindness lesson]:
1. corank distribution over random rational stacks AND raw random words
   (every word is WB-solvable at the boundary - the system is underdetermined);
2. the known ceiling constructions: adjacent monomial pairs (x^a, x^{a-1});
3. adversarial max-|BAD| search with corank classification;
4. for anchored stacks: |BAD| vs the proven budget (w+1)+n(w+1)+1 and vs the
   incidence count of the Cramer family.
"""
import random
from collections import Counter
from itertools import combinations
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(8128)

def wb_any_solution(inst, u):
    """At/above boundary every word is WB-solvable; return one (l, R)."""
    q, n, k, w = inst.q, inst.n, inst.k, inst.w
    ncol = (w + 1) + (w + k)
    M = []
    for i, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u[i] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    rk, ker = rank_and_kernel(M, q, want_kernel=True)
    for v in ker:
        l = pnorm(list(v[:w + 1]))
        r = pnorm(list(v[w + 1:]))
        if l:
            return l, r
    return None

def corank_of(inst, l0, r0, l1, r1):
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    mr = 0
    for gam in range(inst.q):
        M = [[(M0[i][j] + gam * M1[i][j]) % inst.q for j in range(ncol)]
             for i in range(len(M0))]
        rk, _ = rank_and_kernel(M, inst.q)
        mr = max(mr, rk)
    return ncol - mr, ncol, len(M0)

def run(q, n, k, w, g, n_random=250, n_words=120):
    inst = Inst(q, n, k, w, g)
    budget = (w + 1) + n * (w + 1) + 1
    print(f"\n=== boundary instance (q,n,k,w)=({q},{n},{k},{w}) "
          f"[n=2w+k={2*w+k}] budget={budget} dom={inst.dom} ===", flush=True)
    stats = Counter()
    maxbad = {}
    # 1. random rational stacks
    for _ in range(n_random):
        l0 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
            continue
        u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
        if u0 is None or u1 is None:
            continue
        ck, ncol, rows = corank_of(inst, l0, r0, l1, r1)
        B = bad_set(inst, u0, u1)
        tag = ("anchored" if ck <= 1 else f"corank{ck}")
        stats[("rat", tag)] += 1
        key = ("rat", tag)
        maxbad[key] = max(maxbad.get(key, 0), len(B))
        if len(B) > budget:
            print(f"  BUDGET VIOLATION rat: |BAD|={len(B)} ck={ck}", flush=True)
    # 2. raw random words (boundary: always WB-solvable)
    for _ in range(n_words):
        u0 = [random.randrange(q) for _ in range(n)]
        u1 = [random.randrange(q) for _ in range(n)]
        s0 = wb_any_solution(inst, u0)
        s1 = wb_any_solution(inst, u1)
        if s0 is None or s1 is None:
            stats[("word", "nosol")] += 1
            continue
        l0, r0 = s0
        l1, r1 = s1
        ck, ncol, rows = corank_of(inst, l0, r0, l1, r1)
        B = bad_set(inst, u0, u1)
        tag = ("anchored" if ck <= 1 else f"corank{ck}")
        stats[("word", tag)] += 1
        key = ("word", tag)
        maxbad[key] = max(maxbad.get(key, 0), len(B))
        if len(B) > budget:
            print(f"  BUDGET VIOLATION word: |BAD|={len(B)} ck={ck}", flush=True)
    # 3. adjacent monomial pairs (the KKH26-style ceiling shape): u0=x^a, u1=x^{a-1}
    for a in range(1, min(2 * k, n)):
        u0 = [pow(x, a, q) for x in inst.dom]
        u1 = [pow(x, a - 1, q) for x in inst.dom]
        s0 = wb_any_solution(inst, u0)
        s1 = wb_any_solution(inst, u1)
        if s0 is None or s1 is None:
            continue
        l0, r0 = s0
        l1, r1 = s1
        ck, _, _ = corank_of(inst, l0, r0, l1, r1)
        B = bad_set(inst, u0, u1)
        tag = ("anchored" if ck <= 1 else f"corank{ck}")
        print(f"  adjacent pair a={a}: |BAD|={len(B)} class={tag}"
              + ("  <<< BUDGET VIOLATION" if len(B) > budget else ""), flush=True)
    print(f"stats: {dict(stats)}")
    print(f"max |BAD| per class: { {k_: v for k_, v in sorted(maxbad.items(), key=str)} }")

# (17, 8, 4, 2): mu8 in F17, generator 2 (2^8 = 256 = 1 mod 17)
run(17, 8, 4, 2, 2)
# (37, 12, 8, 2): mu12 in F37 — find a generator of order 12
q = 37
g12 = None
for cand in range(2, q):
    if pow(cand, 12, q) == 1 and all(pow(cand, d, q) != 1 for d in (1, 2, 3, 4, 6)):
        g12 = cand
        break
print(f"\nF37 mu12 generator: {g12}")
run(37, 12, 8, 2, g12, n_random=150, n_words=60)
