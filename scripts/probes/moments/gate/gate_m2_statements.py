#!/usr/bin/env python3
"""Numeric gate for the AgreementMomentTwo.lean statements (issue #334, M2 brick).

A correct Lean proof of a mis-transcribed statement is still a wrong brick; this
gate transcribes the designed statements LITERALLY from the Lean text (truncated
Nat subtraction and all) and checks them against brute-force enumeration BEFORE
any proof effort is spent.

Transcribed Lean definition (AgreementMomentTwo.pairAgreementCount):
  def pairAgreementCount (q d e j1 j2 : Nat) : Nat :=
    sum over s in Finset.Iic (min j1 j2) of
      e.choose s * (q - 1) ^ (e - s)
        * d.choose (j1 - s) * (d - (j1 - s)).choose (j2 - s)
        * (q - 2) ^ (d - (j1 - s) - (j2 - s))
with EVERY subtraction truncated at 0 (Nat).

TARGET 1 (card_exact_pair_agreement): for any f, g : [n] -> [q],
  #{u : #{x : u x = f x} = j1 and #{x : u x = g x} = j2}
    = pairAgreementCount(q, d, e, j1, j2),  d = #{x : f x != g x}, e = n - d.

TARGET 2 (sum_agreement_spectrum_sq): for the RS code polysDegLT k on D,
  sum_u a_j(u)^2 = q^k * sum_{c in code} pairAgreementCount(q, wt c, n - wt c, j, j).

TARGET 3: a_j(u0)^2 <= RHS of TARGET 2 for every u0 (direction spot-check).

Exit 0 iff every check passes (exact integers).
"""

import itertools
import sys
from math import comb

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("GATE FAIL:", msg)


def nsub(a, b):
    """Nat truncated subtraction."""
    return a - b if a >= b else 0


def pair_agreement_count(q, d, e, j1, j2):
    """LITERAL transcription of the Lean definition (left-assoc truncated subs)."""
    total = 0
    for s in range(0, min(j1, j2) + 1):  # Finset.Iic (min j1 j2)
        t1 = nsub(j1, s)
        t2 = nsub(j2, s)
        total += (comb(e, s)
                  * nsub(q, 1) ** nsub(e, s)
                  * comb(d, t1)
                  * comb(nsub(d, t1), t2)
                  * nsub(q, 2) ** nsub(nsub(d, t1), t2))
    return total


# ---------- TARGET 1: generic pair-agreement count ----------

def brute_pair_count(n, q, f, g, j1, j2):
    cnt = 0
    for u in itertools.product(range(q), repeat=n):
        if sum(u[x] == f[x] for x in range(n)) == j1 and \
           sum(u[x] == g[x] for x in range(n)) == j2:
            cnt += 1
    return cnt


def gate_target1():
    cases = []
    # n=4, q=5: d = 0, 1, 2, 4
    cases += [(4, 5, (0, 1, 2, 3), (0, 1, 2, 3)),       # d=0
              (4, 5, (0, 1, 2, 3), (0, 1, 2, 4)),       # d=1
              (4, 5, (0, 1, 2, 3), (0, 1, 4, 0)),       # d=2
              (4, 5, (0, 1, 2, 3), (1, 2, 3, 4))]       # d=4
    # n=5, q=7: mixed
    cases += [(5, 7, (0, 1, 2, 3, 4), (0, 1, 2, 5, 6)),  # d=2
              (5, 7, (3, 3, 3, 3, 3), (4, 4, 3, 3, 3))]  # d=2 constant-ish
    # q=2 edge (the (q-2)^e = 0^e branch) and q=3 (type-E q-3 = 0)
    cases += [(4, 2, (0, 1, 0, 1), (1, 1, 0, 0)),        # q=2, d=2
              (4, 3, (0, 1, 2, 0), (1, 1, 2, 2))]        # q=3, d=3
    for (n, q, f, g) in cases:
        d = sum(f[x] != g[x] for x in range(n))
        e = n - d
        for j1 in range(n + 1):
            for j2 in range(n + 1):
                brute = brute_pair_count(n, q, f, g, j1, j2)
                lean = pair_agreement_count(q, d, e, j1, j2)
                if brute != lean:
                    fail(f"T1 n={n} q={q} f={f} g={g} d={d} (j1,j2)=({j1},{j2}): "
                         f"brute={brute} lean={lean}")
    print(f"[gate] T1: {len(cases)} (f,g) cases x all (j1,j2) checked")


# ---------- TARGET 2: the M2 identity on the RS code ----------

def codewords(q, k, domain):
    n = len(domain)
    pows = [[pow(x, e, q) for e in range(k)] for x in domain]
    return [tuple(sum(cf[e] * pows[i][e] for e in range(k)) % q for i in range(n))
            for cf in itertools.product(range(q), repeat=k)]


def gate_target2():
    setups = [(5, 2, [1, 2, 3, 4]),
              (7, 2, [1, 2, 4, 6]),   # non-subgroup domain
              (7, 3, [1, 2, 4, 6]),   # k=3, non-subgroup
              (5, 3, [1, 2, 3, 4])]
    for (q, k, dom) in setups:
        n = len(dom)
        cws = codewords(q, k, dom)
        # brute LHS: sum_u a_j(u)^2 for all j
        lhs = [0] * (n + 1)
        max_aj_sq = [0] * (n + 1)  # for TARGET 3
        for u in itertools.product(range(q), repeat=n):
            hist = [0] * (n + 1)
            for cw in cws:
                hist[sum(ci == ui for ci, ui in zip(cw, u))] += 1
            for j in range(n + 1):
                lhs[j] += hist[j] ** 2
                max_aj_sq[j] = max(max_aj_sq[j], hist[j] ** 2)
        # Lean RHS: q^k * sum_c pairAgreementCount(q, wt c, n - wt c, j, j)
        for j in range(n + 1):
            rhs = q ** k * sum(
                pair_agreement_count(q,
                                     sum(ci != 0 for ci in cw),
                                     n - sum(ci != 0 for ci in cw),
                                     j, j)
                for cw in cws)
            if lhs[j] != rhs:
                fail(f"T2 q={q} k={k} D={dom} j={j}: brute={lhs[j]} lean-RHS={rhs}")
            # TARGET 3 direction: max_u a_j(u)^2 <= RHS
            if max_aj_sq[j] > rhs:
                fail(f"T3 q={q} k={k} j={j}: max a_j^2 = {max_aj_sq[j]} > RHS {rhs}")
        print(f"[gate] T2+T3: q={q} k={k} D={dom} all j checked")


if __name__ == "__main__":
    gate_target1()
    gate_target2()
    if FAILS:
        print(f"GATE: {FAILS} FAILURES")
        sys.exit(1)
    print("GATE: all statements faithful (T1, T2, T3)")
    sys.exit(0)
