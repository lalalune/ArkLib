#!/usr/bin/env python3
"""WB window pencil: WHICH CLASS carries the w+1 extremals? (#371)

Follow-up to probe_wb_window_pencil_crt.py (reformulation validated, 0 mismatches).
Here: adversarially search for max-|BAD| genuine rational pairs at (13,6,1,2),
including the sigma-invariant family (sigma: x -> -1/x on mu6 in F13, orbits
1<->12, 4<->3, 9<->10), and classify every high-bad pair by pencil degeneracy:

  - nondeg  : full column rank at some gamma  => minors give #EXPL <= w+1 (theorem)
  - DEGEN   : kernel at every gamma           => the residual case

Key outputs: max |BAD| per class; whether extremal (w+1) pairs are nondeg;
max |BAD| within DEGEN; kernel dimension stats for DEGEN pairs.
"""
import random
from collections import Counter
from itertools import combinations, product

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# reuse helpers by inlining (probe files are standalone by convention)
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(7)

q, n, k, w, g = 13, 6, 1, 2, 4
inst = Inst(q, n, k, w, g)
sigma = {}
for x in inst.dom:
    sigma[x] = (-pow(x, q - 2, q)) % q
print(f"dom={inst.dom} sigma-orbits: {sorted((min(a,b),max(a,b)) for a,b in sigma.items() if a<=b)}")

def classify(l0, r0, l1, r1):
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    P, ranks = pencil_expl_set(inst, M0, M1, dims)
    maxrank = max(ranks.values())
    degen = maxrank < ncol
    # kernel dim at generic gamma (= ncol - maxrank)
    return ("DEGEN" if degen else "nondeg"), ncol - maxrank, P

def word_sigma_invariant(u):
    return all(u[inst.dom.index(sigma[inst.dom[i]])] == u[i] for i in range(n))

best = Counter()        # class -> max bad
best_pairs = {}
samples = 0
found_ext = []

def consider(l0, r0, l1, r1):
    global samples
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        return
    u0 = inst.ratword(l0, r0)
    u1 = inst.ratword(l1, r1)
    if u0 is None or u1 is None:
        return
    samples += 1
    B = bad_set(inst, u0, u1)
    if len(B) < 2:
        return
    tag, kdim, P = classify(l0, r0, l1, r1)
    inv = word_sigma_invariant(u0) and word_sigma_invariant(u1)
    key = (tag, kdim)
    if len(B) > best[key]:
        best[key] = len(B)
        best_pairs[key] = (l0, r0, l1, r1, sorted(B), inv)
    if len(B) >= w + 1:
        found_ext.append((tag, kdim, len(B), inv, (l0, r0, l1, r1)))
        print(f"EXTREMAL |BAD|={len(B)} class={tag} kerdim={kdim} sigma-inv={inv} "
              f"pair l0={l0} r0={r0} l1={l1} r1={r1} bad={sorted(B)}", flush=True)

# 1) heavy random search
for _ in range(20000):
    l0 = [random.randrange(q) for _ in range(3)]
    r0 = [random.randrange(q) for _ in range(3)]
    l1 = [random.randrange(q) for _ in range(3)]
    r1 = [random.randrange(q) for _ in range(3)]
    consider(l0, r0, l1, r1)

# 2) sigma-invariant rational words: u sigma-invariant <=> u constant on orbits.
# enumerate ALL sigma-invariant words (q^3 each row), keep rational genuine ones.
# rationality: u = R/l with l deg<=2 nonvanishing: test by Welch-Berlekamp solve.
def wb_rational(u):
    # find (l, R), deg l <= w, deg R <= w+k-1, l(x_i) u_i = R(x_i), l nonzero on dom,
    # gcd(l, R) = 1, deg l >= 1 (genuine)
    for ld in range(1, w + 1):
        # monic l of degree ld
        for lc in product(range(q), repeat=ld):
            l = list(lc) + [1]
            if any(peval(l, x, q) == 0 for x in inst.dom):
                continue
            # R determined by interpolation conditions? deg R <= w+k-1 = 2, n=6 eqs
            M = []
            for i, x in enumerate(inst.dom):
                row = [pow(x, j, q) for j in range(w + k)]
                M.append(row + [peval(l, x, q) * u[i] % q])
            r1_, _ = rank_and_kernel([row[:-1] for row in M], q)
            r2_, _ = rank_and_kernel(M, q)
            if r1_ != r2_:
                continue
            # solve for R
            rk, ker = rank_and_kernel(
                [row[:-1] + [(-row[-1]) % q] for row in M] , q, want_kernel=True)
            # solve M[:, :-1] R = M[:, -1] -- use augmented kernel trick:
            # kernel of [A | -b] with last coord 1 gives solution
            sol = None
            for v in ker:
                if v[-1] != 0:
                    invl = pow(v[-1], q - 2, q)
                    sol = [c * invl % q for c in v[:-1]]
                    break
            if sol is None:
                continue
            R = pnorm(sol)
            if len(pgcd(l, R, q)) == 1 and pnorm(l) and len(pnorm(l)) >= 2:
                return l, R
    return None

orbit_reps = [1, 4, 9]
inv_words = []
for vals in product(range(q), repeat=3):
    u = [0] * n
    for rep, v in zip(orbit_reps, vals):
        u[inst.dom.index(rep)] = v
        u[inst.dom.index(sigma[rep])] = v
    inv_words.append(tuple(u))
print(f"sigma-invariant words: {len(inv_words)}; finding rational ones...", flush=True)
rat_inv = []
for u in inv_words:
    wb = wb_rational(u)
    if wb is not None:
        rat_inv.append((u, wb))
print(f"rational genuine sigma-invariant words: {len(rat_inv)}", flush=True)
# all PAIRS of rational invariant words (cap to keep runtime sane)
random.shuffle(rat_inv)
capped = rat_inv[:60]
for i in range(len(capped)):
    for j in range(len(capped)):
        if i == j:
            continue
        (u0, (l0, r0)), (u1, (l1, r1)) = capped[i], capped[j]
        consider(l0, r0, l1, r1)

print(f"\nsamples with genuine pairs considered: {samples}")
print("max |BAD| by (class, generic kernel dim):")
for key, v in sorted(best.items()):
    l0, r0, l1, r1, B, invf = best_pairs[key]
    print(f"  {key}: max|BAD|={v} sigma-inv={invf} bad={B} pair=({l0},{r0},{l1},{r1})")
print(f"\nextremal (>=w+1={w+1}) pairs found: {len(found_ext)}")
cc = Counter((t, d, inv) for t, d, _, inv, _ in found_ext)
print(f"extremal class histogram (class, kerdim, sigma-inv): {dict(cc)}")
