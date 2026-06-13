#!/usr/bin/env python3
"""
probe_smooth_listsize_energy.py  (#389 — proximity prize, list-decoding side)

QUESTION PROBED
  Does the multiplicative structure of a smooth domain mu_n = <g> in F_q (the prize's
  evaluation set for plain Reed-Solomon RS[mu_n, k]) HELP or HURT the list size in the
  beyond-Johnson window  delta in (1 - sqrt(rho), 1 - rho),  rho = k/n  — versus a generic
  evaluation set of the same size?

  The list at agreement threshold t is  max over words w of  #{ deg-<k polys p : p agrees
  with w on >= t coords of mu_n }.  For k=2 this is the count of distinct lines through >= t
  of the n points (x_i, w_i); for general k it is interpolants of k-subsets, deduped.

WHY IT MATTERS
  The prize reduces (via I(delta) <= ell/(delta'-delta), ell = close-codeword curve degree)
  to bounding the list size of plain RS on mu_n in the window. Combinatorial / moment methods
  give only Johnson; the open question is whether mu_n's structure keeps the list poly (prize
  TRUE) or blows it up (prize FALSE / delta* pinned below capacity).

FINDING 1 — RANDOM-SAMPLED list (UNDER-estimate, field sweep, n=8,k=2,t=3, in window)
    q      E/n^2   Sidon(q>2^n)   list mu_n    list generic
    17     4.12    no             7            7
    41     3.12    no             7            6
    73-113 2.62    no             5            5
    257+   2.62    yes            4            4     (q=1153: 4 vs 3)
  Random sampling SYSTEMATICALLY under-estimates the worst-case list. Use FINDING 2.

FINDING 2 — WORST-CASE list via hill-climbing (RELIABLE; `worst_list`), rho=1/4, delta=0.625
    n   q     worst mu_n   worst generic   capacity = 1/(1-rho-delta)
    8   73    7            6               8
    8   257   6            6               8
    8   1153  5            4               8
    12  1549  8            8               12
  => CORRECTED PICTURE (supersedes the over-optimistic random read):
     (a) The worst-case list is a SUBSTANTIAL FRACTION of capacity (~0.6-0.8), NOT small.
     (b) mu_n is ~ GENERIC, in fact SLIGHTLY WORSE (>= generic in 3/4 instances) — the
         multiplicative structure gives NO list advantage; there is no structural miracle.
     (c) The energy correlation survives but is mild (7->6->5 as field grows to the Sidon
         floor); the dominant term is ~ capacity, which is O(1/eta), eta = 1-rho-delta.
     (d) Near the window EDGE (delta -> 1-rho, eta -> 0) capacity -> infinity, so the list
         BLOWS UP; the prize is exactly HOW it blows up (poly in 1/eta?). Small-n probes
         CANNOT resolve this asymptotic — it is the open core.

HONEST BOTTOM LINE
  * energy->list is provably sqrt-LOSSY (issue389-additive-energy-crux): even E=t^2 gives list
    n^{3/2}. Energy is NOT a tight prize lever; these probes are diagnostic, not a proof route.
  * mu_n ~ generic experimentally => the prize for plain RS is neither obviously true nor false
    from small n; it hinges on the asymptotic curve-degree / higher-order-MDS behavior, which is
    the recognized open problem (R1/R3 in PROXIMITY_PRIZE_WORKBENCH.lean).

USAGE
  python3 probe_smooth_listsize_energy.py        # field sweep (FINDING 1) + worst-case (FINDING 2)
"""
import itertools, math, random
from collections import Counter


def find_subgroup(q, n):
    """Return sorted mu_n = order-n multiplicative subgroup of F_q (q prime, n | q-1)."""
    if (q - 1) % n != 0:
        return None
    for prg in range(2, q):
        order, x = 1, prg % q
        while x != 1:
            x = (x * prg) % q
            order += 1
        if order == q - 1:  # primitive root found
            h = pow(prg, (q - 1) // n, q)
            S, v = set(), 1
            for _ in range(n):
                S.add(v)
                v = (v * h) % q
            return sorted(S)
    return None


def add_energy(S, q):
    """Additive energy E(S) = #{(a,b,c,d) in S^4 : a+b = c+d}."""
    c = Counter()
    for a in S:
        for b in S:
            c[(a + b) % q] += 1
    return sum(v * v for v in c.values())


def line_through(x1, y1, x2, y2, q):
    m = ((y2 - y1) * pow((x2 - x1) % q, q - 2, q)) % q
    return (m, (y1 - m * x1) % q)


def max_list_lines(q, D, t, trials, seed=7):
    """k=2: max over sampled words of #{distinct lines hitting >= t of (x_i, w_i)}."""
    n = len(D)
    random.seed(seed)
    best = 0
    for _ in range(trials):
        m0, b0 = random.randrange(q), random.randrange(q)
        w = [(m0 * x + b0) % q for x in D]
        for _ in range(random.randint(1, n)):
            w[random.randrange(n)] = random.randrange(q)
        rich = set()
        for i in range(n):
            for j in range(i + 1, n):
                L = line_through(D[i], w[i], D[j], w[j], q)
                if L in rich:
                    continue
                if sum(1 for a in range(n) if (L[0] * D[a] + L[1]) % q == w[a]) >= t:
                    rich.add(L)
        best = max(best, len(rich))
    return best


def _evalp(c, x, q):
    r = 0
    for a in reversed(c):
        r = (r * x + a) % q
    return r


def _interp_vals(xs, ys, D, q, inv):
    """Values on D of the deg-<len(xs) interpolant through (xs, ys); inv = inverse table."""
    out = []
    k = len(xs)
    for x in D:
        tot = 0
        for i in range(k):
            num, den = ys[i], 1
            for j in range(k):
                if j == i:
                    continue
                num = num * ((x - xs[j]) % q) % q
                den = den * ((xs[i] - xs[j]) % q) % q
            tot = (tot + num * inv[den]) % q
        out.append(tot)
    return tuple(out)


def _listsize(w, D, k, t, q, inv):
    n = len(D)
    seen, cnt = set(), 0
    for sub in itertools.combinations(range(n), k):
        vals = _interp_vals([D[i] for i in sub], [w[i] for i in sub], D, q, inv)
        if vals in seen:
            continue
        seen.add(vals)
        if sum(1 for a in range(n) if vals[a] == w[a]) >= t:
            cnt += 1
    return cnt


def worst_list(q, D, k, t, restarts=60, steps=400, seed=3):
    """RELIABLE worst-case list via random-restart hill-climbing over the adversarial word.
    Returns max over searched words of #{deg-<k polys agreeing with w on >= t coords of D}."""
    n = len(D)
    random.seed(seed)
    inv = [0] * q
    for a in range(1, q):
        inv[a] = pow(a, q - 2, q)
    best = 0
    for _ in range(restarts):
        c0 = tuple(random.randrange(q) for _ in range(k))
        w = [_evalp(c0, x, q) for x in D]
        for _ in range(random.randint(n // 2, n)):
            w[random.randrange(n)] = random.randrange(q)
        cur = _listsize(w, D, k, t, q, inv)
        for _ in range(steps):
            i, old = random.randrange(n), None
            old = w[i]
            w[i] = random.randrange(q)
            nv = _listsize(w, D, k, t, q, inv)
            if nv >= cur:
                cur = nv
            else:
                w[i] = old
        best = max(best, cur)
    return best


def main():
    n, t, TR = 8, 3, 200000  # k=2 lines; window k=2 < t=3 < sqrt(nk)=4
    print(f"== FINDING 1: random-sampled (UNDER-estimate) ==  n={n} k=2 t={t}  Sidon E/n^2 -> {(3 * n * n - 3 * n) / n**2:.2f}")
    print(f"{'q':>6} {'E/n^2':>7} {'Sidon?':>7} {'list mu_n':>10} {'generic':>8}")
    for q in [17, 41, 73, 113, 257, 1153]:
        if (q - 1) % n != 0:
            continue
        D = find_subgroup(q, n)
        print(f"{q:>6} {add_energy(D, q) / n**2:>7.2f} {str(q > 2**n):>7} "
              f"{max_list_lines(q, D, t, TR):>10} {max_list_lines(q, list(range(1, n + 1)), t, TR):>8}")
    print(f"\n== FINDING 2: WORST-CASE via hill-climbing (RELIABLE) ==  rho=1/4, delta=0.625")
    print(f"{'n':>3} {'k':>2} {'t':>2} {'q':>6} {'worst mu_n':>11} {'worst generic':>14} {'cap':>5}")
    for (nn, q) in [(8, 73), (8, 257), (8, 1153), (12, 1549)]:
        k = nn // 4
        tt = max(k + 1, int(round(0.375 * nn)))
        D = find_subgroup(q, nn)
        cap = 1 / (1 - k / nn - (1 - tt / nn))
        print(f"{nn:>3} {k:>2} {tt:>2} {q:>6} {worst_list(q, D, k, tt):>11} "
              f"{worst_list(q, list(range(1, nn + 1)), k, tt):>14} {cap:>5.1f}", flush=True)


if __name__ == "__main__":
    main()
