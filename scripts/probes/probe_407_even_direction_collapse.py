#!/usr/bin/env python3
"""
probe_407_even_direction_collapse.py  (#407)

Refutes the OPEN Prop `EvenDirectionIncidenceCollapse` (EvenDirectionDescent.lean) — the REVERSE leg
of the 2-adic even-direction far-line-incidence descent.

EvenDirectionDescent.lean proves the FORWARD leg unconditionally:
    explainableScalars(RS[mu_{n/2}, k], delta', u0', u1')
      SUBSET  explainableScalars(RS[mu_n, 2k], delta, u0'of, u1'of)   [even dir x^{2a'} on mu_n]
i.e.  I_{n/2}  injects into  I_n(even)  (half-domain bad => full-domain even-direction bad).

The clean 2-adic identity I_n(even) = I_{n/2} (the prize-useful descent) needs the REVERSE
containment I_n(even) SUBSET I_{n/2}, named `EvenDirectionIncidenceCollapse` and NOT proved (the
file flags: the RS[mu_n,2k] codeword explaining the full line need not be the even pullback of an
RS[mu_{n/2},k] codeword -- its ODD part can carry agreement on a non-fibre-symmetric witness set).

This probe computes BOTH bad-sets EXACTLY (Lagrange max-agreement over all K-subsets) and tests the
reverse containment in the binding band.

RESULT (n=16, k=2, binding band s_half=3 / s_full=6):
  p=97 : |I_n(even)|=56 > |I_{n/2}|=40 ; REVERSE FAILS. 16 scalars (e.g. 14,17,21,23) are bad for the
         full even direction on mu_16 (max-agreement 6 >= 6 with deg<4) but their squaring-descent on
         mu_8 has max-agreement only 2 < 3 (NOT bad). => EvenDirectionIncidenceCollapse is FALSE.
  p=113: |I_n(even)|=40 = |I_{n/2}|=40 ; holds (prime-dependent).
So the reverse collapse is FALSE in general (prime-dependent), confirming the file's honest caveat with
explicit witnesses: the odd part of the full-domain codeword carries non-descending agreement.

Verified independently (verify): gamma in {14,17,21,23} at p=97 each have full-agreement=6, half-agreement=2.
"""
import sympy
from itertools import combinations


def max_agreement(domain, K, target, p):
    D = len(domain); best = 0
    for sub in combinations(range(D), K):
        xs = [domain[i] for i in sub]; ys = [target[i] for i in sub]
        if len(set(xs)) < K:
            continue
        ag = 0
        for i in range(D):
            x = domain[i]; val = 0
            for j in range(K):
                num = 1; den = 1
                for l in range(K):
                    if l == j:
                        continue
                    num = num * ((x - xs[l]) % p) % p
                    den = den * ((xs[j] - xs[l]) % p) % p
                val = (val + ys[j] * num * pow(den, p - 2, p)) % p
            if val == target[i] % p:
                ag += 1
        best = max(best, ag)
        if best >= D:
            break
    return best


def bad_set(domain, K, u0, u1, s_thr, p):
    out = set()
    for gamma in range(p):
        target = [(u0[i] + gamma * u1[i]) % p for i in range(len(domain))]
        if max_agreement(domain, K, target, p) >= s_thr:
            out.add(gamma)
    return out


def primes_mod1(n, count, pmin):
    res = []; k = max(1, pmin // n + 1)
    while len(res) < count:
        q = k * n + 1
        if sympy.isprime(q) and q > n + 1:
            res.append(q)
        k += 1
    return res


def main():
    print("=== EvenDirectionIncidenceCollapse (reverse leg) — refutation probe ===")
    a = 4; n = 1 << a; nh = n >> 1; k = 2
    for p in primes_mod1(n, 2, pmin=4 * n):
        g = sympy.primitive_root(p)
        omn = pow(g, (p - 1) // n, p); omh = pow(omn, 2, p)
        dom_n = [pow(omn, i, p) for i in range(n)]
        dom_h = [pow(omh, i, p) for i in range(nh)]
        cprime = k; aprime = k + 1
        u0h = [pow(x, cprime, p) for x in dom_h]; u1h = [pow(x, aprime, p) for x in dom_h]
        u0f = [pow(x, 2 * cprime, p) for x in dom_n]; u1f = [pow(x, 2 * aprime, p) for x in dom_n]
        for s_half in (k + 1, k + 2, k + 3):
            s_full = 2 * s_half
            Bn = bad_set(dom_n, 2 * k, u0f, u1f, s_full, p)
            Bh = bad_set(dom_h, k, u0h, u1h, s_half, p)
            fwd = Bh.issubset(Bn); rev = Bn.issubset(Bh)
            print(f"n={n} p={p} s_half={s_half} s_full={s_full}: |I_n(even)|={len(Bn)} "
                  f"|I_n/2|={len(Bh)} fwd={fwd} rev={rev} EQ={Bn == Bh}", flush=True)
            if fwd and not rev:
                extra = sorted(Bn - Bh)
                print(f"    REVERSE FAILS: {len(extra)} scalars full-even-bad but half-NOT-bad: {extra[:8]}",
                      flush=True)


if __name__ == "__main__":
    main()
