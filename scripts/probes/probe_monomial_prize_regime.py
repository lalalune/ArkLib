#!/usr/bin/env python3
"""
probe_monomial_prize_regime.py  (issue #389) -- CORRECTION of probe_monomial_extremal.py

RESULT (decisive): at the only tractable PRIZE-LIKE point RS[mu_10,k=5]/F_11, w=3, delta=0.30
(ABOVE Johnson 0.293, avg incidence ~7 ~ n=10), the best MONOMIAL direction gives incidence 10
but a NON-monomial direction gives 11, and ALL sampled far directions beat the monomial max.
=> 'monomials extremal' is REFUTED in the prize regime; monomials are SUB-optimal there. The
cyclic lever gives only a delta* UPPER bracket (monomials as a construction), NOT the worst case.
(Below Johnson, w=2: monomials DO survive -- opposite regime behaviour, as in the small-code probe.)

The earlier probe's "above-Johnson" points were NOT prize-like: they were either saturated
(I ~ q) or had NO far cosets (I = 0, because at w = n-k the weight-<=w ball already covers the
whole syndrome space). The genuine PRIZE regime is:

    small incidence  I ~ n << q     (the q*eps* ~ n scale),
    radius in the WINDOW interior    (above Johnson 1-sqrt(rho), below capacity 1-rho).

For that to occur ABOVE Johnson one needs w <= (n-k)-2 still above Johnson, which forces n >= 10,
with q large enough that |S_w|/q^{n-k} ~ n/q is small. Then q^{n-k} is far too big to enumerate s0.

KEY TRICK (no q^{n-k} loop): for a fixed direction s1, the offsets s0 partition F_q^m into lines in
direction s1. The max incidence over s0 is the MAX NUMBER OF S_w-POINTS ON A LINE in direction s1 --
computed by bucketing the |S_w| points by their s1-line, O(|S_w|) per direction. So we can reach
large q. We compute I_mono (max over monomial directions, EXACT) and sample many random far
directions, checking whether any beats I_mono -> a strong (sampled) test of "monomials extremal" in
a genuine prize-like point.
"""

import itertools
import random


def gf_inv_table(q):
    inv = [0] * q
    for a in range(1, q):
        for b in range(1, q):
            if (a * b) % q == 1:
                inv[a] = b
                break
    return inv


def roots_of_unity(q, n):
    assert (q - 1) % n == 0
    for g in range(2, q):
        x, seen = 1, set()
        for _ in range(q - 1):
            x = (x * g) % q
            seen.add(x)
        if len(seen) == q - 1:
            omega = pow(g, (q - 1) // n, q)
            return [pow(omega, i, q) for i in range(n)]
    raise RuntimeError("no generator")


def null_space(q, M, ncols, inv):
    A = [row[:] for row in M]
    nrows = len(A)
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if A[i][c] % q), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        ip = inv[A[r][c] % q]
        A[r] = [(x * ip) % q for x in A[r]]
        for i in range(nrows):
            if i != r and A[i][c] % q:
                f = A[i][c] % q
                A[i] = [(A[i][j] - f * A[r][j]) % q for j in range(ncols)]
        pivots.append(c); r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for ri, pc in enumerate(pivots):
            v[pc] = (-A[ri][fc]) % q
        basis.append(v)
    return basis


def syn(q, H, word):
    return tuple(sum(H[r][i] * word[i] for i in range(len(word))) % q for r in range(len(H)))


def low_weight_syndromes(q, H, n, w):
    S = {tuple([0] * len(H))}
    for wt in range(1, w + 1):
        for supp in itertools.combinations(range(n), wt):
            for vals in itertools.product(range(1, q), repeat=wt):
                e = [0] * n
                for idx, pos in enumerate(supp):
                    e[pos] = vals[idx]
                S.add(syn(q, H, e))
    return S


def max_fiber(q, s1, Sw, m, inv):
    """max over s0 of #{gamma : s0 + gamma*s1 in Sw} = max # of Sw-points collinear in dir s1."""
    j = next(i for i in range(m) if s1[i] % q)
    ij = inv[s1[j] % q]
    buckets = {}
    best = 0
    for p in Sw:
        t = (p[j] * ij) % q
        rep = tuple((p[i] - t * s1[i]) % q for i in range(m))  # canonical pt on the line (coord j = 0)
        c = buckets.get(rep, 0) + 1
        buckets[rep] = c
        if c > best:
            best = c
    return best


def run(q, n, k, w, n_samples=600, seed_list=range(600)):
    inv = gf_inv_table(q)
    mu = roots_of_unity(q, n)
    G = [[pow(mu[i], j, q) for i in range(n)] for j in range(k)]
    H = null_space(q, G, n, inv)
    m = len(H)
    Sw = list(low_weight_syndromes(q, H, n, w))
    Swset = set(Sw)
    johnson = 1 - (k / n) ** 0.5
    delta = w / n
    avg = len(Sw) / q ** (m - 1)
    zone = "ABOVE-J" if delta > johnson else "below-J"
    # monomial directions x^a, a in {k..n-1}, far (syn not in S_w, nonzero)
    I_mono, mono_arg = 0, None
    for a in range(k, n):
        sa = syn(q, H, [pow(mu[i], a, q) for i in range(n)])
        if sa in Swset or not any(sa):
            continue
        f = max_fiber(q, sa, Sw, m, inv)
        if f > I_mono:
            I_mono, mono_arg = f, ("x^%d" % a, sa)
    # sample random far directions, check if any beats I_mono
    I_samp, samp_arg, beats = 0, None, 0
    rng = random.Random(12345)
    tried = 0
    for _ in range(n_samples):
        s1 = tuple(rng.randrange(q) for _ in range(m))
        if not any(s1) or s1 in Swset:
            continue
        tried += 1
        f = max_fiber(q, s1, Sw, m, inv)
        if f > I_samp:
            I_samp, samp_arg = f, s1
        if f > I_mono:
            beats += 1
    print(f"RS[mu_{n},k={k}] /F_{q}  rho={k/n:.3f} q/n={q/n:.1f}  w={w} delta={delta:.3f} "
          f"[{zone} J={johnson:.3f}]  m={m}")
    print(f"   |S_w|={len(Sw)}  avg_incidence(=|S_w|/q^(m-1))={avg:.2f}  (prize-like iff small, ~n={n})")
    print(f"   I_mono (exact over monomials) = {I_mono}   [{mono_arg[0] if mono_arg else '-'}]")
    print(f"   I_sampled ({tried} random far dirs) = {I_samp}   #dirs beating mono = {beats}")
    if beats == 0:
        print(f"   -> monomials achieve the max over all {tried} sampled directions (mono extremal: SURVIVES)")
    else:
        print(f"   -> {beats} sampled direction(s) BEAT the monomial max (mono extremal: REFUTED here)")
        print(f"      best sampled dir s1={samp_arg} gives {I_samp} > {I_mono}")
    print()
    return (I_mono, I_samp, beats, avg, zone)


if __name__ == "__main__":
    print("PRIZE-REGIME test of 'monomials extremal' via bucketing (reaches large q):\n")
    # n>=10 so that w <= m-2 can be above Johnson with small incidence.
    cases = [
        (11, 10, 5, 3),   # PRIZE-LIKE: m=5 w=3 delta=0.30 > J=0.293, avg incidence ~7 ~ n
        (11, 10, 5, 2),   # below-J control (delta=0.20 < J)
    ]
    results = []
    for (q, n, k, w) in cases:
        try:
            results.append(((q, n, k, w), run(q, n, k, w)))
        except Exception as ex:
            print(f"SKIP {(q,n,k,w)}: {ex}\n")
    print("=" * 70)
    prize = [(c, r) for (c, r) in results if r[4] == "ABOVE-J" and 1 < r[3] <= 3 * c[1]]
    refuted = [(c, r) for (c, r) in prize if r[2] > 0]
    print(f"Prize-like points (above-J, small avg incidence): {len(prize)}")
    print(f"Of those, monomial-extremal REFUTED: {len(refuted)}")
    if not prize:
        print("VERDICT: still no clean prize-like point reached.")
    elif refuted:
        print("VERDICT: 'monomials extremal' REFUTED in a prize-like point -> cyclic-closure")
        print("         path gives only a delta* upper bracket (mono = lower bound on worst case).")
    else:
        print("VERDICT: monomials extremal at every prize-like point sampled -> cyclic-closure")
        print("         path survives in the genuine prize regime (small I, above Johnson).")
