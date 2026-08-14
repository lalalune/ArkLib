#!/usr/bin/env python3
"""
THE DECISIVE #444 MEASUREMENT (comment 4708838551, lalalune):

  The 1-D far-line incidence is proven SUP-BLIND (RealizerL2NotSup: annihilator b.s1=0 over a
  field => only principal eta_0=|G| survives => incidence = |G| = n, CONSTANT across primes
  where B=max_{b!=0}||eta_b|| DIFFERS).  THE OPEN QUESTION: is the GENUINE >=2-D MCA incidence
  -- the actual prize object epsMCA(C,delta) = max_{u0,u1} #{gamma : mcaEvent C delta u0 u1
  gamma}/q (ABF26 Def 4.3, real witness SETS of size (1-delta)n, real codewords, the joint
  non-agreement clause) -- ALSO B-independent (=> delta* L2/computable, wall IRRELEVANT, MAJOR)
  or does it RE-COUPLE to the sup B (=> wall stays)?

DECISIVE TEST (the test lalalune used for the 1-D case): hold (n,k) FIXED; pick primes
p = 1 mod n where the 1-D subgroup sup B DIFFERS (structured/Fermat primes blow B up,
generic primes keep it small); compute the EXACT epsMCA worst-case bad-gamma COUNT (the
in-tree mcaEvent, syndrome-reduced engine cross-checked vs naive word-level in
probe_exact_epsmca_ladder.py).  Then:

  * if the worst-case COUNT is CONSTANT across primes-with-different-B (after removing the
    trivial 1/p in epsMCA=count/p) => epsMCA is ALSO B-blind (L2/computable) => MAJOR reframe.
  * if the COUNT tracks B (varies, larger where B is larger) => epsMCA RE-COUPLES to the sup.

We compare the raw bad-gamma COUNT (numerator), NOT epsMCA=count/q -- because count/q always
shrinks like 1/p trivially; the B-coupling question is about the NUMERATOR (how many bad
scalars the witness-set structure produces), which is what carries any spectral dependence.

CRITICAL DISCIPLINE: PROPER smooth mu_n (n=2^a, n|p-1), p chosen to give DIFFERENT B, exact
exhaustive mcaEvent (no sampling), NEVER n=q-1.  Uses probe_exact_epsmca_ladder.eps_profile_*
(the validated in-tree engine).
"""
import importlib.util, os, math, cmath, sys
from itertools import combinations

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ladder)


def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5) + 1):
        if m % d == 0: return False
    return True


def primes_cong1(n, lo, count):
    out = []; p = lo - (lo % n) + 1
    if p < lo: p += n
    while len(out) < count:
        if p > 2 and p % n == 1 and is_prime(p):
            out.append(p)
        p += n
    return out


def subgroup(n, p):
    """mu_n = order-n subgroup of F_p^* (n | p-1)."""
    return ladder.smooth_domain(p, n)


def sup_B(mu, p):
    """B = max_{b!=0} | sum_{x in mu} e_p(b x) | -- the 1-D subgroup period sup (the open wall)."""
    w = 2j * math.pi / p
    B = 0.0; argmax = None
    for b in range(1, p):
        s = 0j
        for x in mu:
            s += cmath.exp(w * ((b * x) % p))
        m = abs(s)
        if m > B:
            B = m; argmax = b
    return B, argmax


def exact_epsmca_counts(p, n, k):
    """Exact worst-case bad-gamma COUNT per witness-size threshold m (the in-tree mcaEvent,
    syndrome-reduced).  Returns {m: max bad-gamma count}."""
    best, subsets = ladder.eps_profile_syndrome(p, n, k)
    return best


def main():
    # (n, k) instances small enough for EXACT exhaustive mcaEvent over p^{2(n-k)} syndrome pairs.
    # n MUST be a 2-power (proper smooth mu_n) for the prize geometry.  Keep n-k small.
    plans = [
        # n, k, prime-search-lo, n_primes : the exhaustive cost is ~ p^{2(n-k)} * p, so keep small.
        (4, 2, 60, 6),   # rho=1/2, n-k=2: p^4*p enumeration, fine to a few hundred
        (4, 3, 60, 6),   # rho=3/4, n-k=1: very cheap
        (8, 6, 80, 4),   # rho=3/4, n-k=2: p^4*p, keep p modest
    ]
    for (n, k, lo, npr) in plans:
        primes = primes_cong1(n, lo, npr)
        rho = k / n
        print(f"\n{'='*78}")
        print(f"RS[mu_{n}, k={k}]  rho={rho:.3f}  Johnson={1-math.sqrt(rho):.3f}  "
              f"capacity={1-rho:.3f}   (EXACT in-tree mcaEvent, syndrome-reduced)")
        print(f"{'='*78}")
        rows = []
        for p in primes:
            mu = subgroup(n, p)
            B, bargmax = sup_B(mu, p)
            counts = exact_epsmca_counts(p, n, k)
            rows.append((p, B, counts))
        # print B per prime
        print("  per-prime 1-D subgroup sup  B = max_{b!=0}||eta_b||:")
        for (p, B, _) in rows:
            print(f"     p={p:>6}   B={B:>9.5f}   B/sqrt(n)={B/math.sqrt(n):>7.4f}")
        Bs = [r[1] for r in rows]
        Bspread = (max(Bs) - min(Bs)) / (sum(Bs) / len(Bs))
        print(f"  -> B rel-spread across these primes = {Bspread:.5f}  "
              f"(min {min(Bs):.4f}, max {max(Bs):.4f})")
        # for each witness threshold m, print the exact bad-gamma count across primes
        ms = sorted(rows[0][2].keys(), reverse=True)
        print(f"\n  {'m':>3} {'delta':>7} | " +
              " ".join(f"p={p:<6}" for (p, _, _) in rows) +
              " | count-spread  VERDICT")
        for m in ms:
            delta = 1 - m / n
            cs = [r[2][m] for r in rows]
            line = f"  {m:>3} {delta:>7.3f} | " + " ".join(f"{c:<8}" for c in cs)
            mean_c = sum(cs) / len(cs)
            if mean_c == 0:
                verdict = "(all 0)"
                cspread = 0.0
            else:
                cspread = (max(cs) - min(cs)) / mean_c
                # does the COUNT track B? compare count-spread vs B-spread
                if cspread < 0.02 and Bspread > 0.03:
                    verdict = "CONSTANT (B-blind)"
                elif cspread > 0.4 * Bspread and Bspread > 0.03:
                    verdict = "TRACKS B (re-couples)"
                else:
                    verdict = "~constant"
            print(line + f" | {cspread:>10.4f}  {verdict}")
        # Per-prime correlation: is the prime with MAX B also the prime with MAX count anywhere?
        pmaxB = max(rows, key=lambda r: r[1])[0]
        pminB = min(rows, key=lambda r: r[1])[0]
        print(f"\n  prime with MAX B = {pmaxB}, prime with MIN B = {pminB}")
        # check if any threshold has the counts ordered the same as B
        coupled_any = False
        for m in ms:
            cmaxB = dict((p, c) for (p, _, cs) in rows for mm, c in cs.items() if mm == m)
            # gather (B, count) and check monotone correlation
            pairs = sorted((r[1], r[2][m]) for r in rows)
            counts_by_B = [c for (_, c) in pairs]
            if len(set(counts_by_B)) > 1 and counts_by_B == sorted(counts_by_B):
                coupled_any = True
        print(f"  any threshold with bad-count monotone-increasing in B? {coupled_any}")


if __name__ == "__main__":
    main()
