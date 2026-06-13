#!/usr/bin/env python3
"""
probe_ld_mca_gap.py  (#389, Fable, 2026-06-12)

THE LD => MCA GAP, measured for k=2 on a smooth domain.

The exact sub-Johnson LIST size is now pinned (fleet: char-0 ladder census = N_fib).
But delta* is governed by the MCA functional (mutual correlated agreement), which is
STRICTLY stronger than list-decoding: ABF26 Def 4.3 -- gamma is MCA-bad for a stack
(u0,u1) at radius delta iff some witness set S with |S| >= a=(1-delta)n has
  (i)  the LINE u0+gamma*u1 matching a codeword on S, AND
  (ii) the PAIR (u0,u1) NOT jointly matched on that SAME S
       (no codewords c0,c1 with c0=u0 and c1=u1 on S).

For k=2 (affine codewords y=alpha x+beta), a word matches a codeword on S iff its graph
restricted to S is collinear. So gamma is MCA-bad iff some >=a-subset of the domain is
collinear in the (D_i, (u0+gamma u1)(D_i)) graph BUT not simultaneously collinear in BOTH
the u0-graph and the u1-graph on the same subset.

This probe computes, on mu_n in F_p, for ladder/monomial stacks across sub-Johnson radii:
  - LIST size of u0+gamma*u1 (= max #codewords agreeing >= a, i.e. # a-rich affine lines);
  - the MCA-BAD scalar count (# gamma firing mcaEvent);
to measure whether MCA << LD (=> floor better than list => delta* near capacity) or
MCA ~ LD (the LD=>MCA collapse, = delta* tracks the list).

Smooth domain: mu_n = n-th roots of unity in F_p (needs n | p-1).
"""
from itertools import combinations
from collections import defaultdict

def roots_of_unity(p, n):
    # find an element of order n in F_p^*  (n | p-1)
    assert (p - 1) % n == 0
    for g in range(2, p):
        # g is a generator candidate; order check
        if pow(g, (p - 1) // n, p) != 1 and pow(g, (p-1), p) == 1:
            # candidate primitive-ish; get element of exact order n
            h = pow(g, (p - 1) // n, p)
            if all(pow(h, d, p) != 1 for d in range(1, n)):
                return [pow(h, i, p) for i in range(n)]
    raise RuntimeError("no order-n element")

def affine_agreement_lines(D, vals, p, a):
    """Return list of (alpha,beta, frozenset S) for affine lines agreeing with the word
    (D_i -> vals_i) on >= a points.  Lines determined by pairs; dedup."""
    n = len(D)
    seen = {}
    # also constant/degenerate via pairs; for >=a>=3 lines are determined by any 2 agreeing pts
    for i in range(n):
        for j in range(i + 1, n):
            dx = (D[i] - D[j]) % p
            if dx == 0:
                continue
            alpha = ((vals[i] - vals[j]) * pow(dx, p - 2, p)) % p
            beta = (vals[i] - alpha * D[i]) % p
            if (alpha, beta) in seen:
                continue
            S = frozenset(t for t in range(n) if (alpha * D[t] + beta) % p == vals[t])
            if len(S) >= a:
                seen[(alpha, beta)] = S
    return list(seen.items())

def graph_collinear_on(D, vals, S, p):
    """Is the word's graph collinear on subset S (|S|>=2)?  (affine-explainable on S)"""
    S = list(S)
    if len(S) <= 2:
        return True
    i, j = S[0], S[1]
    dx = (D[i] - D[j]) % p
    if dx == 0:
        return False
    alpha = ((vals[i] - vals[j]) * pow(dx, p - 2, p)) % p
    beta = (vals[i] - alpha * D[i]) % p
    return all((alpha * D[t] + beta) % p == vals[t] for t in S)

def mca_bad(D, u0, u1, gamma, p, a):
    """Is gamma MCA-bad?  Check witness sets S = agreement sets of a-rich lines of the
    word w = u0 + gamma*u1, and test the mutual (joint) failure on that S."""
    n = len(D)
    w = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    lines = affine_agreement_lines(D, w, p, a)
    for (_, S) in lines:
        # (i) holds by construction (line matches w on S, |S|>=a).
        # (ii): pair NOT jointly matched on S  <=>  NOT (u0|S collinear AND u1|S collinear)
        joint = graph_collinear_on(D, u0, S, p) and graph_collinear_on(D, u1, S, p)
        if not joint:
            return True
    return False

def list_size(D, u0, u1, gamma, p, a):
    w = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    return len(affine_agreement_lines(D, w, p, a))

from math import comb

def witness_mass_law(n, a, q, k=2):
    """The failure-side prediction: MCA-bad ~ min(q, C(n,a)/q^m), band m = a-k-1
    (a = k+m+1, so the witness-mass density is C(n,k+m+1)/q^m)."""
    m = a - k - 1
    if m < 0:
        return q
    return min(q, comb(n, a) // max(1, q ** m))

def run(p, n, stack_name, u0, u1, show=True):
    D = run.D
    if show:
        print(f"\n=== p={p} n={n} stack={stack_name} ===")
        print(f"{'a':>3} {'delta':>7} {'#MCA-bad':>9} {'wmass-law':>10} "
              f"{'maxlist':>8} {'regime':>14}")
    table = {}
    for a in range(3, n):
        bad = 0
        maxlist_all = 0
        for gamma in range(p):
            ls = list_size(D, u0, u1, gamma, p, a)
            maxlist_all = max(maxlist_all, ls)
            if mca_bad(D, u0, u1, gamma, p, a):
                bad += 1
        table[a] = bad
        if show:
            delta = 1 - a / n
            reg = ("sub-Johnson" if a * a < 2 * 1 * n else "above-Johnson")
            wm = witness_mass_law(n, a, p)
            print(f"{a:>3} {delta:>7.3f} {bad:>9} {wm:>10} {maxlist_all:>8} {reg:>14}")
    return table

def run_named(p, n, stack_name, u0f, u1f):
    D = roots_of_unity(p, n)
    run.D = D
    u0 = [u0f(x, p) for x in D]
    u1 = [u1f(x, p) for x in D]
    return run(p, n, stack_name, u0, u1)

# ladder-ish stacks over mu_n; k=2 so u1 = x^2 (the x^k direction row)
n = 8
run_named(41, 8, "u0=x^4 (ladder)", lambda x, p: pow(x, 4, p), lambda x, p: pow(x, 2, p))
n = 16
run_named(97, 16, "u0=x^8 (ladder)", lambda x, p: pow(x, 8, p), lambda x, p: pow(x, 2, p))

# THE DECISIVE TEST: does ANY stack EXCEED the witness-mass law?  Scan many stack types
# (random words + adversarial monomials) and record the MAX #MCA-bad per band vs the law.
print("\n\n############ ADVERSARIAL MAX-OVER-STACKS vs WITNESS-MASS LAW ############")
print("(if max #MCA-bad over all tested stacks <= witness-mass law, the ceiling is the")
print(" actual delta* = the Calibrated Pin survives at the MCA level; an EXCESS refutes it)")
import random
def scan(p, n, ntrials=400, seed=12345):
    D = roots_of_unity(p, n)
    run.D = D
    rng = random.Random(seed)
    maxbad = {a: 0 for a in range(3, n)}
    argmax = {a: None for a in range(3, n)}
    # structured stacks
    structured = []
    for e0 in range(3, n):
        structured.append((f"x^{e0}", [pow(x, e0, p) for x in D], [pow(x, 2, p) for x in D]))
    # random stacks
    for _ in range(ntrials):
        u0 = [rng.randrange(p) for _ in D]
        u1 = [rng.randrange(p) for _ in D]
        structured.append(("rand", u0, u1))
    for name, u0, u1 in structured:
        for a in range(3, n):
            b = sum(1 for g in range(p) if mca_bad(D, u0, u1, g, p, a))
            if b > maxbad[a]:
                maxbad[a] = b; argmax[a] = name
    print(f"\n--- p={p} n={n} ({ntrials} random + {n-3} monomial stacks) ---")
    print(f"{'a':>3} {'delta':>7} {'MAX#bad':>8} {'wmass-law':>10} {'argmax':>8} {'verdict':>14}")
    for a in range(3, n):
        wm = witness_mass_law(n, a, p)
        verdict = "EXCEEDS LAW" if maxbad[a] > wm else "<= law"
        print(f"{a:>3} {1-a/n:>7.3f} {maxbad[a]:>8} {wm:>10} {str(argmax[a]):>8} {verdict:>14}")

def q_independence(n, primes, e_list):
    """Show the worst-case MCA-bad count N_a is q-INDEPENDENT (structural), not the
    q-decreasing second-moment witness mass C(n,a)/q^m.  Reports N_a = max over the
    monomial stacks (x^e, x^2) of the bad count, per agreement a, per prime."""
    print(f"\n############ q-INDEPENDENCE OF THE WORST-CASE STRUCTURAL COUNT N_a ############")
    print(f"(n={n}; N_a = max_e #MCA-bad(x^e, x^2); compare across q — flat => structural)")
    for a in range(3, 6):
        row = []
        for p in primes:
            D = roots_of_unity(p, n)
            run.D = D
            best = 0
            for e in e_list:
                u0 = [pow(x, e, p) for x in D]; u1 = [pow(x, 2, p) for x in D]
                b = sum(1 for g in range(p) if mca_bad(D, u0, u1, g, p, a))
                best = max(best, b)
            row.append(best)
        wm = [witness_mass_law(n, a, p) for p in primes]
        print(f"  a={a} (delta={1-a/n:.3f}): N_a over q={primes} = {row}  "
              f"| witness-mass C(n,a)/q^m = {wm}")

if __name__ == "__main__":
    scan(41, 8, ntrials=300)
    scan(97, 16, ntrials=150)
    q_independence(16, [193, 257, 449, 577], list(range(3, 16)))
    print("\nFINDINGS (reproducible, q-stable):")
    print("1. The worst-case MCA-bad count N_a is Q-INDEPENDENT structural (e.g. N_4=97,")
    print("   N_5=2 flat across q on mu_16) — NOT the q-decreasing witness mass C(n,a)/q^m.")
    print("2. The worst case is a SPECIFIC monomial (x^9 at a=4), not the ladder and not the")
    print("   second-moment family — so the second moment is not the worst-case mechanism.")
    print("3. delta*(q) = 1 - a_min/n, a_min = min{a : N_a <= eps*.q = q.2^-128}: a STAIRCASE")
    print("   in q. The exact pin reduces to the growth of N_a (the divisor-census max over")
    print("   stacks) in the agreement a — q-independent, structural, the sharp open object.")
