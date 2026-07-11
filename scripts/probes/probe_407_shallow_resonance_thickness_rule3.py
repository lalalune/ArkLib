# Rule-3 (thinness-essential) test on the SHALLOW e2=0 over-det resonance closed form K(n,k+2)=n/4-1.
#
# CONTEXT (#444, DISPROOF_LOG 2026-06-15):
#   - The shallow e2=0 census orbit-count was pinned EXACT: K(n, w=k+2) = n/4 - 1, p-independent (char-0),
#     #bad = n*K = n^2/4 - n  (the Theta(n^2) over-det object). Tied to wf-D2's s*-k = n/4.
#   - Sibling commit 417015191 proved the e2=0 census (at w=n/2) is THINNESS-ESSENTIAL: it VANISHES for
#     RANDOM domains (antipodal-pairing mechanism). That control is RANDOM-set vanishing.
#   - The general-k probe just showed K(n,k+2)=n/4-1 is k-INDEPENDENT and the resonance delta=1-(k+2)/n
#     is IN-WINDOW (below cap=1-k/n) for every tested k -> NOT excluded above cap.
#
# THE UNCONTESTED OPEN EDGE (rule-3, a DIFFERENT control than 417015191's random-set):
#   Is the n/4-1 resonance THIN-ESSENTIAL against the PROPER THICK 2-power/multiplicative-subgroup control
#   (beta in the prize-FALSE thick window 2.3-3.2), or does the SAME n/4-1 appear in thick subgroups?
#   - If K(n,k+2) = n/4 - 1 for THICK subgroups too (e.g. mu_n with n=q^{1/2.3}) => the resonance count
#     is THICKNESS-INVARIANT => rule-3 FAIL => the shallow resonance is NOT a thin-essential prize lever
#     (it is a generic cyclotomic-antipodal count of the 2-power group structure, present whenever -1 in mu_n).
#   - If K differs (thick gives a different / vanishing value) => the n/4-1 resonance IS thin-essential
#     at the shallow width and the R1 floor object survives rule-3 there.
#
# Both controls share the SAME 2-power group mu_n (so -1 in mu_n, antipodal pairing intact); only the
# field size q (=> beta = log_n q) changes. This isolates THICKNESS (beta), not negation-closure.
# This is the rule-3 control 417015191 did NOT run (random-set, not thick-subgroup).
#
# proper subgroup always; multiple primes per (n,beta); never n=q-1.

import itertools, math
from sympy import isprime, primitive_root

def first_primes_beta(n, beta, count=2, start_mult=1):
    """primes p with n | p-1, p ~ n^beta, p != n+1-trivial; return `count` of them."""
    target = int(round(n**beta))
    p = target - (target % n) + 1
    out = []
    # search upward then downward around n^beta
    cand = p
    tries = 0
    while len(out) < count and tries < 200000:
        if cand > n and (cand - 1) % n == 0 and isprime(cand):
            out.append(cand)
        cand += n
        tries += 1
    return out

def K_shallow(n, p, w):
    """orbit-count K of e1-values for e2=0, e1!=0 width-w subsets of mu_n; #bad = n*K."""
    g = pow(primitive_root(p), (p - 1) // n, p)
    mu = [pow(g, j, p) for j in range(n)]
    e1set = set()
    cnt = 0
    for S in itertools.combinations(range(n), w):
        s1 = 0; s2 = 0
        for i in S:
            v = mu[i]; s1 += v; s2 += v * v
        if (s1 * s1 - s2) % p == 0 and s1 % p != 0:
            cnt += 1
            e1set.add((-pow(s1, p - 2, p)) % p)
    # collapse e1-values into mu_n dilation orbits
    rem = set(e1set); K = 0
    while rem:
        x = next(iter(rem))
        rem -= set((u * x) % p for u in mu)
        K += 1
    return cnt, len(e1set), K

print("RULE-3 thickness test on the SHALLOW e2=0 resonance closed form K(n,w=4) = n/4 - 1.")
print("Same 2-power group mu_n (antipodal intact); vary beta = log_n(q). THIN(prize) beta>=4 vs THICK beta~2.3-3.2.")
print("If K = n/4-1 in BOTH => thickness-INVARIANT => rule-3 FAIL (not a thin lever). If THIN-only => survives.\n")

k = 2
w = k + 2  # the shallow resonance width 4
for n in [16, 32]:
    pred = n // 4 - 1
    print(f"=== n={n}  predicted thin n/4-1 = {pred}  (w={w}) ===")
    for beta in [2.3, 3.0, 4.0, 5.0]:
        if math.comb(n, w) > 30_000_000:
            print(f"  beta={beta}: C({n},{w}) too big"); continue
        primes = first_primes_beta(n, beta, count=2)
        if not primes:
            print(f"  beta={beta}: no prime found near n^beta"); continue
        results = []
        for p in primes:
            cnt, dist, K = K_shallow(n, p, w)
            results.append((p, K, cnt))
        kvals = sorted(set(r[1] for r in results))
        tag = "THICK(prize-FALSE)" if beta < 3.5 else "THIN(prize)"
        match = "== n/4-1" if all(r[1] == pred for r in results) else "!= n/4-1"
        detail = ", ".join(f"p={p}:K={K}(#bad={n*K})" for p, K, cnt in results)
        print(f"  beta={beta} [{tag:18s}] K={kvals} {match:9s} | {detail}")
    print()
print("VERDICT: read whether K=n/4-1 holds across ALL beta (thickness-invariant => rule-3 FAIL)")
print("or only thin beta>=4 (=> shallow resonance is thin-essential).")

# ---------------------------------------------------------------------------
# DISAMBIGUATION control (rule-6 adversarial): is the n/4-1 value set by the SUBGROUP
# structure, or merely by NEGATION-CLOSURE? 417015191 showed fully-random vanishes (needs
# negation). Here: a NEGATION-CLOSED RANDOM set (random {+/-x_i} pairs, NOT a subgroup) --
# does it ALSO give K=n/4-1 (=> value is pure negation-closure, even weaker / more generic)
# or a DIFFERENT value (=> value needs the cyclic 2-power subgroup, not just negation)?
import random as _r
print("\n--- DISAMBIGUATION: negation-closed RANDOM set (not a subgroup), same n, prize prime ---")
for n in [16, 32]:
    pred = n // 4 - 1
    # build a prize prime
    p = int(round(n**4)); p = p - (p % n) + 1
    while not ((p - 1) % n == 0 and isprime(p)):
        p += n
    g = primitive_root(p)
    Ks = []
    for trial in range(4):
        # pick n/2 random nonzero residues, close under negation -> negation-closed random set of size n
        half = set()
        while len(half) < n // 2:
            x = _r.randrange(1, p)
            if x != (p - x) and x not in half and (p - x) not in half:
                half.add(x)
        D = list(half) + [(p - x) % p for x in half]  # negation-closed, |D|=n, NOT a subgroup
        e1set = set(); cnt = 0
        for S in itertools.combinations(range(n), w):
            s1 = 0; s2 = 0
            for i in S:
                v = D[i]; s1 += v; s2 += v * v
            if (s1 * s1 - s2) % p == 0 and s1 % p != 0:
                cnt += 1; e1set.add((-pow(s1, p - 2, p)) % p)
        # orbit-collapse under the SUBGROUP mu_n (the dilation symmetry of the problem)
        mu = [pow(g, (p - 1) // n * j % (p - 1), p) for j in range(n)]
        rem = set(e1set); K = 0
        while rem:
            x = next(iter(rem)); rem -= set((u * x) % p for u in mu); K += 1
        Ks.append((cnt, len(e1set), K))
    cnts = [c for c, d, k in Ks]
    print(f"  n={n} neg-random (4 draws): #bad(raw e2=0 sets)={cnts}  subgroup-pred n/4-1={pred}  "
          f"=> {'matches subgroup count' if all(c == n*pred for c in cnts) else 'DIFFERS from n/4-1 (value needs the subgroup, not just negation)'}")
print("\nINTERPRETATION: subgroup THICK+THIN all = n/4-1 (above) => beta-invariant. If neg-random DIFFERS,")
print("the n/4-1 value is a SUBGROUP-cyclotomic count, beta-invariant => negation-essential but NOT")
print("thinness-essential => rule-3 FAIL as a prize lever (the prize is FALSE in the thick window).")
