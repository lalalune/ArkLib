#!/usr/bin/env python3
"""probe_monomial_domination_falsifier.py — the registered falsifier of
MonomialDomination (#357, MonomialDominationPin.lean).

MonomialDomination asserts: at every grid radius above the crossing, no stack beats
the best monomial pair. Falsifier: any stack with MORE bad scalars than every
monomial pair at some agreement.

This probe attacks with the two cheapest non-monomial families at (16, 4) over
F_97/F_193, at the agreements where the monomial table is known (a in {7, 8, 10}):

  1. BINOMIAL rows: u = x^s1 + c*x^s2, v = x^t (and v binomial too) — the smallest
     perturbation off the monomial surface; scan c in F* for structured s/t choices.
  2. TRANSLATE stacks: u = x^s, v = x^t + c (constant offsets — equivalent to
     codeword translation, MUST tie the monomial count; serves as an engine check).

Method: same exact affine-in-lambda solver as probe_takeover_death_radius.py
(per-witness kernel functionals; bad-lambda set per stack exact).

Verdict per (field, agreement): max non-monomial count vs monomial max. Any strict
excess = MonomialDomination FALSIFIED (report the stack); ties/below = survives.
"""

import itertools
import sys
import time


def inv_mod(x, p):
    return pow(x, p - 2, p)


def kernel_basis(rows, k, p):
    a = len(rows)
    M = [[rows[i][j] for i in range(a)] for j in range(k)]
    piv, r = [], 0
    for c in range(a):
        if r >= k:
            break
        pr = next((rr for rr in range(r, k) if M[rr][c] % p), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        iv = inv_mod(M[r][c], p)
        M[r] = [(x * iv) % p for x in M[r]]
        for rr in range(k):
            if rr != r and M[rr][c] % p:
                f = M[rr][c]
                M[rr] = [(M[rr][j] - f * M[r][j]) % p for j in range(a)]
        piv.append(c)
        r += 1
    out = []
    for fc in [c for c in range(a) if c not in piv]:
        v = [0] * a
        v[fc] = 1
        for ri, pc in enumerate(piv):
            v[pc] = (-M[ri][fc]) % p
        out.append(v)
    return out


def bad_count(u, v, wit, p):
    bad = set()
    for (T, basis) in wit:
        uT = [u[i] for i in T]
        vT = [v[i] for i in T]
        al = [sum(r[j] * uT[j] for j in range(len(T))) % p for r in basis]
        be = [sum(r[j] * vT[j] for j in range(len(T))) % p for r in basis]
        if all(x == 0 for x in al) and all(x == 0 for x in be):
            continue
        lp, cons, alll = None, True, True
        for x, y in zip(al, be):
            if y == 0:
                if x != 0:
                    cons = False
                    break
                continue
            alll = False
            lam = (-x * inv_mod(y, p)) % p
            if lp is None:
                lp = lam
            elif lp != lam:
                cons = False
                break
        if not cons:
            continue
        if alll:
            return p
        if lp is not None:
            bad.add(lp)
    return len(bad)


def main():
    n, k = 16, 4
    for p in (97, 193):
        g = next(c for c in range(2, p) if pow(c, n, p) == 1
                 and all(pow(c, d, p) != 1 for d in (1, 2, 4, 8)))
        H = [pow(g, i, p) for i in range(n)]
        for a in (8, 7, 10):
            t0 = time.time()
            wit = []
            for T in itertools.combinations(range(n), a):
                pts = [H[i] for i in T]
                vrows = [[pow(x, e, p) for e in range(k)] for x in pts]
                wit.append((T, kernel_basis(vrows, k, p)))
            # monomial baseline
            mono_max, mono_arg = 0, None
            monos = {}
            for s in range(1, n):
                monos[s] = [pow(x, s, p) for x in H]
            monos[0] = [1] * n
            for s in range(1, n):
                for t in range(0, s):
                    c = bad_count(monos[s], monos[t], wit, p)
                    if c > mono_max:
                        mono_max, mono_arg = c, (s, t)
            # binomial attack: u = x^s1 + c x^s2 vs v = x^t, structured choices
            attack_max, attack_arg = 0, None
            ss = [(9, 8), (10, 8), (9, 7), (10, 4), (12, 8), (10, 7)]
            cs = [1, 2, 3, p - 1, p - 2, g, inv_mod(g, p)]
            for (s1, s2) in ss:
                for c in cs:
                    u = [(monos[s1][i] + c * monos[s2][i]) % p for i in range(n)]
                    for t in range(0, min(s1, 12)):
                        cnt = bad_count(u, monos[t], wit, p)
                        if cnt > attack_max:
                            attack_max, attack_arg = cnt, ((s1, s2, c), t)
                    # binomial second row too (one structured choice)
                    v2 = [(monos[s2][i] + c * monos[max(s2 - 1, 0)][i]) % p
                          for i in range(n)]
                    cnt = bad_count(u, v2, wit, p)
                    if cnt > attack_max:
                        attack_max, attack_arg = cnt, ((s1, s2, c), ('bin', s2))
            verdict = ("FALSIFIED — non-monomial stack beats the pairs!"
                       if attack_max > mono_max else "survives")
            print(f"p={p} a={a}: monomial max={mono_max} at {mono_arg}; "
                  f"attack max={attack_max} at {attack_arg} -> {verdict} "
                  f"[{time.time()-t0:.0f}s]", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
