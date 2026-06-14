#!/usr/bin/env python3
"""Probe (#389): ADVERSARIAL test of "L_max(a) = max_towers N_fib(s,r)" at scale.

Goal: try to BREAK the subset-sum fibre law. Search many non-ladder word families
for a single-word sub-Johnson list exceeding the best ladder/fibre value:
  - ladder words x^{rm}+lam x^{(r-1)m} at fibre-maximal lam (the conjectured optimum)
  - MULTI-fibre words: sums of two/three ladder terms / cross-tower mixes
  - coset-built words: constant on cosets of subgroups of various orders
  - near-code + garbage
  - random + hill-climb from every structured seed (objective = list size at a)

If anything exceeds the ladder value -> the law is REFUTED and the deviation is the
lead. If nothing does across scales/primes -> the law strengthens toward exact.
"""
import itertools, random, sys
from collections import Counter


def find_g(p, n):
    for h in range(2, 2000):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    return None


def list_size(w, a, xs, p, K):
    """#distinct deg<K codewords with agreement >= a with w (dedup over k-subsets)."""
    N = len(xs)
    seen = set()
    # only need codewords; iterate k-subsets, interpolate, dedup, keep agreement>=a
    for T in itertools.combinations(range(N), K):
        pts = [xs[i] for i in T]
        vals = [w[i] for i in T]
        cw = []
        ok = True
        for x in xs:
            tot = 0
            for ii in range(K):
                num, den = 1, 1
                for jj in range(K):
                    if ii == jj: continue
                    num = num * ((x - pts[jj]) % p) % p
                    den = den * ((pts[ii] - pts[jj]) % p) % p
                tot = (tot + vals[ii] * num * pow(den, -1, p)) % p
            cw.append(tot)
        if sum(1 for i in range(N) if cw[i] == w[i]) >= a:
            seen.add(tuple(cw))
    return len(seen)


def nfib(xs, p, m, r):
    mus = sorted({pow(x, m, p) for x in xs})
    fib = Counter()
    for T in itertools.combinations(mus, r):
        fib[sum(T) % p] += 1
    sm, cnt = fib.most_common(1)[0]
    return cnt, (-sm) % p, len(mus)


def ladder(xs, p, m, r, lam):
    return [(pow(x, r * m, p) + lam * pow(x, (r - 1) * m, p)) % p for x in xs]


def run(N, K, p, towers, bands, rng, do_hillclimb=True):
    g = find_g(p, N)
    if g is None:
        print(f"  (no order-{N} element mod {p})"); return
    xs = [pow(g, i, p) for i in range(N)]
    print(f"\n==== (n,k)=({N},{K}), p={p}, g={g} ====", flush=True)
    # fibre prediction + the ladder words
    pred = {}
    lads = []
    for (m, r) in towers:
        cnt, lam, s = nfib(xs, p, m, r)
        for a in bands:
            if r * m >= a:
                pred[a] = max(pred.get(a, 0), cnt)
        lads.append((m, r, lam, cnt))
        print(f"  tower m={m},r={r} (s={s}): N_fib={cnt}, rm={r*m}", flush=True)
    # adversarial candidate words (besides ladders)
    def candidates():
        cands = []
        # multi-fibre: sum of two ladder terms from different towers
        for (m1, r1, l1, _) in lads:
            for (m2, r2, l2, _) in lads:
                if (m1, r1) >= (m2, r2): continue
                w = [(ladder(xs, p, m1, r1, l1)[i] + ladder(xs, p, m2, r2, l2)[i]) % p
                     for i in range(N)]
                cands.append((f"mix({m1}r{r1}+{m2}r{r2})", w))
        # coset-built: w(i) = random constant on cosets of subgroup of order d
        for d in [t for t in (2, 4, 8) if N % t == 0]:
            vals = {j: rng.randrange(p) for j in range(d)}
            w = [vals[i % d] for i in range(N)]
            cands.append((f"coset-d{d}", w))
        # near-code: a codeword (deg<K) plus a few errors
        cw = [(rng.randrange(p) + rng.randrange(p) * xs[i]) % p for i in range(N)]
        for e in (3, 5):
            w = list(cw)
            for _ in range(e): w[rng.randrange(N)] = rng.randrange(p)
            cands.append((f"near-code+{e}", w))
        # three-term ladder
        if lads:
            m, r, lam, _ = max(lads, key=lambda l: l[3])
            w = [(pow(xs[i], r*m, p) + lam*pow(xs[i], (r-1)*m, p)
                  + pow(xs[i], (r+1)*m % (N if N else 1), p)) % p for i in range(N)]
            cands.append(("3term", w))
        return cands

    for a in bands:
        best, who = 0, None
        # ladders
        for (m, r, lam, _) in lads:
            if r * m < a: continue
            L = list_size(ladder(xs, p, m, r, lam), a, xs, p, K)
            if L > best: best, who = L, f"ladder m{m}r{r}"
        ladbest = best
        # adversarial candidates
        for name, w in candidates():
            L = list_size(w, a, xs, p, K)
            if L > best: best, who = L, name
        # generic + hill-climb
        if do_hillclimb:
            seeds = []
            if lads:
                m, r, lam, _ = max((l for l in lads if l[1]*l[0] >= a),
                                   key=lambda l: l[3], default=lads[0])
                seeds.append(ladder(xs, p, m, r, lam))
            seeds.append([rng.randrange(p) for _ in range(N)])
            seeds.append([rng.randrange(p) for _ in range(N)])
            for w0 in seeds:
                w = list(w0); cur = list_size(w, a, xs, p, K)
                for _ in range(30):
                    i, v = rng.randrange(N), rng.randrange(p)
                    old = w[i]; w[i] = v
                    L2 = list_size(w, a, xs, p, K)
                    if L2 >= cur: cur = L2
                    else: w[i] = old
                if cur > best: best, who = cur, "hill-climb"
        flag = ("LAW HOLDS" if best <= pred.get(a, 0)
                else f"*** EXCEEDS PRED {pred.get(a,0)} ***")
        print(f"  a={a}: pred {pred.get(a,0)}, ladder {ladbest}, overall max {best} "
              f"({who})  [{flag}]", flush=True)


def main():
    rng = random.Random(2024)
    # (32,3): two primes
    for p in (97, 193):
        if (p - 1) % 32 == 0:
            run(32, 3, p, [(2, 3), (4, 2), (1, 4)], [6, 7, 8, 9], rng)
    # (32,4): heavier
    for p in (97,):
        if (p - 1) % 32 == 0:
            run(32, 4, p, [(2, 3), (4, 2), (1, 5), (2, 4)], [7, 8, 9], rng)
    # (64,3): structured candidates only (no hill-climb, too slow)
    for p in (193, 257):
        if (p - 1) % 64 == 0:
            run(64, 3, p, [(2, 3), (4, 2), (8, 2), (1, 4)], [7, 8, 9],
                rng, do_hillclimb=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())
