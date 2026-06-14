#!/usr/bin/env python3
"""
probe_line_tower_recursion.py  (#407)

VERIFY THE 2-POWER-TOWER RECURSION for far-line INCIDENCE (linchpin of the closed delta* reframing).

Claim: the imprimitive monomial line (X^{2a'}, X^{2b'}) on mu_n against RS[k] has, at agreement
threshold tau, EXACTLY the incidence of the line (X^{a'}, X^{b'}) on mu_{n/2} against RS[ceil(k/2)]
at agreement threshold ceil(tau/2) -- same gamma set.

Reason: w = X^{2a'}+g X^{2b'} is EVEN (w(y)=w(-y)) = W(y^2), and for p = p_e(y^2)+y p_o(y^2) in RS[k]
the pair {y,-y} BOTH agree iff p_o=0 and p_e=W there, so max agreement on mu_n = 2 * (max agreement
of W with RS[ceil(k/2)] on mu_{n/2}).  This makes the heavy (imprimitive) lines a SELF-SIMILAR
recursion to the half-size subgroup, bottoming at mu_2={+-1}; with delta_avg=1-rho-H(rho)/log2(q) the
SAME for every tower level, the imprimitive incidence never blows up beyond the lower-level worst case.

If the two incidence columns MATCH exactly, recursion confirmed => open core collapses to: does the
PRIMITIVE-direction incidence concentrate (sub-Poisson) at each level.
"""
import numpy as np
from probe_monomial_line_subpoisson import (mu_subgroup, interp_eval_matrices,
                                            line_incidence_profile)


def incidence_one_line(q, n, k, a, b, taus):
    pts = mu_subgroup(q, n)
    mats = interp_eval_matrices(pts, q, k)
    ptsv = np.array(pts, dtype=np.int64)
    u0 = np.ones(n, dtype=np.int64); u1 = np.ones(n, dtype=np.int64)
    for _ in range(a): u0 = (u0 * ptsv) % q
    for _ in range(b): u1 = (u1 * ptsv) % q
    gammas = np.arange(q, dtype=np.int64)
    return line_incidence_profile(u0, u1, mats, q, n, k, gammas, taus)


def main():
    q = 12289
    print("RECURSION CHECK: imprimitive (X^{2a'},X^{2b'}) on mu_n/RS[k]  vs  (X^{a'},X^{b'}) on mu_{n/2}/RS[ceil(k/2)]\n")
    cases = [(8, 2, 1, 3), (8, 4, 1, 3), (8, 3, 1, 3),
             (16, 2, 1, 3), (16, 4, 3, 5), (16, 3, 1, 5)]
    for (n, k, ap, bp) in cases:
        nch, kch = n // 2, (k + 1) // 2
        prof_parent = incidence_one_line(q, n, k, (2 * ap) % n, (2 * bp) % n, list(range(1, n + 1)))
        prof_child = incidence_one_line(q, nch, kch, ap % nch, bp % nch, list(range(1, nch + 1)))
        print(f"=== mu_{n} RS[{k}] line (X^{(2*ap)%n},X^{(2*bp)%n})  <->  mu_{nch} RS[{kch}] line (X^{ap%nch},X^{bp%nch}) ===")
        ok = True
        for tau in range(1, n + 1):
            tc = (tau + 1) // 2
            par = prof_parent.get(tau, 0)
            ch = prof_child.get(tc, None)
            if ch is None:
                continue
            if par != ch:
                ok = False
            if par or ch:
                print(f"   tau={tau:2d} -> child ceil/2={tc:2d}: parent={par:6d}  child={ch:6d}  "
                      f"{'OK' if par==ch else '**MISMATCH**'}")
        print(f"   --> recursion {'CONFIRMED' if ok else 'FAILS'}\n")


if __name__ == "__main__":
    main()
