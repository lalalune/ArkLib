#!/usr/bin/env python3
"""Probe (O113 candidate): the REP-WEIGHT CONE claim — the inductive
strengthening of Lam-Leung.

CLAIM: for squarefree m with prime set P, and any gamma in Z>=0[mu_m] (an
element with at least one N-representation over exponents [0,m)), the set of
total weights of N-representations of gamma is contained in
    mu(gamma) + (N-span of P),
where mu(gamma) is the minimal representation weight.

The gamma = 0 instance is exactly the Lam-Leung N-span law at level m (the
open wall after O112).  If the claim survives, it is the right inductive
strengthening: at n = m*r the thread decomposition c_i(u) = gamma_i + delta(u)
reduces the claim at n to weight bookkeeping at m.

Method: two N-reps of gamma differ by an element of the relation lattice
(= Z-span of prime packets, machine-checked O110).  For random base reps u
over [0,m) with small coordinates, enumerate lattice perturbations
x = sum a_P * P with a_P in [-B, B], keep u + x >= 0, record total weights
N(u) + sum_{p-packets} p*a_P.  Check every achieved weight lies in
(min achieved) + N-span(P).  (The min achieved over the box is an upper bound
for mu; containment of the achieved set in min_achieved + span is NECESSARY
for the claim restricted to the box, and the box already sees the Frobenius
gaps {1,2,4,7,...} that would falsify it.)

RESULT (2026-06-10): the claim is FALSE — offset-1 representation pairs of a
common gamma != 0 exist at EVERY tested modulus (15, 21, 30, 35).  The gamma=0
instance (= Lam-Leung) is untouched; the strengthening dies.  This probe is
kept as the falsification record: exit 0 iff a counterexample IS found at
every modulus (PASS = claim refuted).
"""

import sys
import itertools
import random


def primes_of(n):
    out = []
    m, p = n, 2
    while m > 1:
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
        p += 1
    return out


def packets(n):
    out = []
    for p in primes_of(n):
        step = n // p
        for r in range(step):
            v = [0] * n
            for i in range(p):
                v[r + i * step] = 1
            out.append((p, v))
    return out


def nspan_membership(limit, primes):
    """Boolean table: which totals in [0, limit] are in N-span(primes)."""
    ok = [False] * (limit + 1)
    ok[0] = True
    for t in range(1, limit + 1):
        for p in primes:
            if t >= p and ok[t - p]:
                ok[t] = True
                break
    return ok


def run(m, trials, B, seed):
    rng = random.Random(seed)
    P = packets(m)
    prs = primes_of(m)
    bad = []
    for trial in range(trials):
        u = [rng.randrange(0, 3) for _ in range(m)]
        weights = set()
        # enumerate perturbations over a random subset of packets to keep
        # the box tractable; always include enough of both/all packet types
        idx = list(range(len(P)))
        rng.shuffle(idx)
        chosen = idx[: min(7, len(P))]
        for combo in itertools.product(range(-B, B + 1), repeat=len(chosen)):
            vec = u[:]
            okv = True
            delta_w = 0
            for a, j in zip(combo, chosen):
                if a == 0:
                    continue
                p, pkt = P[j]
                delta_w += p * a
                for e in range(m):
                    if pkt[e]:
                        vec[e] += a
            if all(x >= 0 for x in vec):
                weights.add(sum(u) + delta_w)
        if not weights:
            continue
        w0 = min(weights)
        span_ok = nspan_membership(max(weights) - w0, prs)
        for w in weights:
            if not span_ok[w - w0]:
                bad.append((m, trial, u, w0, w))
                break
        if bad:
            break
    return bad


def main():
    ok = True
    for m, trials, B, seed in [(15, 60, 2, 1), (21, 40, 2, 2),
                               (30, 25, 1, 3), (35, 20, 1, 4)]:
        bad = run(m, trials, B, seed)
        print(f"m={m} trials={trials} B={B}: counterexamples={len(bad)}"
              + ("" if not bad else f" WITNESS(min,bad)={bad[0][3:]}"))
        ok = ok and bool(bad)
    print("PROBE", "PASS (claim REFUTED at every modulus)" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
