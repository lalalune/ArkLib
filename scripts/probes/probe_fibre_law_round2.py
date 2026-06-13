#!/usr/bin/env python3
"""Probe (#389, round 2-3): the subset-sum fibre law at (16,4) and (32,3).

Law: L_max(a) = max over towers n = s*m, rm >= a, (r-2)m < k of
N_fib(s,r) = max subset-sum fibre of r-subsets of mu_s; attained by ladder words.

(16,4) predictions: a=6 -> 3 (m=2,r=3) beats (m=4,r=2)=2; a in {7,8} -> 2 (m=4,r=2);
(32,3) prediction:  a=6 -> max(N_fib(16,3), N_fib(8,2)=4) -- MULTI-TOWER test;
                    a in {7,8} -> N_fib(8,2)=4 (m=4,r=2).
"""
import itertools, random, sys
from collections import Counter


def find_g(p, n):
    for h in range(2, 800):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x


def list_size(w, a, xs, p, K):
    N = len(xs)
    seen = set()
    for T in itertools.combinations(range(N), K):
        pts = [xs[i] for i in T]
        vals = [w[i] for i in T]
        cw = []
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


def nfib(p, xs, m, r):
    mus = sorted({pow(x, m, p) for x in xs})
    fib = Counter()
    for T in itertools.combinations(mus, r):
        fib[sum(T) % p] += 1
    return fib.most_common(1)[0], len(mus)


def ladder(xs, p, m, r, lam):
    return [(pow(x, r * m, p) + lam * pow(x, (r - 1) * m, p)) % p for x in xs]


def run(N, K, p, towers, bands, rng):
    g = find_g(p, N)
    xs = [pow(g, i, p) for i in range(N)]
    print(f"\n==== (n,k)=({N},{K}), p={p} ====", flush=True)
    pred = {}
    lads = []
    for (m, r) in towers:
        (sm, cnt), s = nfib(p, xs, m, r)
        print(f"  tower m={m},r={r} (s={s}): N_fib = {cnt} at sum {sm}, rm = {r*m}")
        for a in bands:
            if r * m >= a:
                pred[a] = max(pred.get(a, 0), cnt)
        lads.append((m, r, (-sm) % p, cnt))
    for a in bands:
        best, who = 0, None
        for (m, r, lam, cnt) in lads:
            if r * m < a: continue
            L = list_size(ladder(xs, p, m, r, lam), a, xs, p, K)
            if L > best: best, who = L, f"ladder m={m} r={r}"
        # adversarial: generic + hill-climb from best ladder
        for t in range(2):
            L = list_size([rng.randrange(p) for _ in range(N)], a, xs, p, K)
            if L > best: best, who = L, f"generic#{t}"
        m, r, lam, _ = max((l for l in lads if l[1] * l[0] >= a),
                           key=lambda l: l[3], default=lads[0])
        w = ladder(xs, p, m, r, lam)
        cur = list_size(w, a, xs, p, K)
        for _ in range(40):
            i, v = rng.randrange(N), rng.randrange(p)
            old = w[i]; w[i] = v
            L2 = list_size(w, a, xs, p, K)
            if L2 >= cur: cur = L2
            else: w[i] = old
        if cur > best: best, who = cur, "hill-climb"
        ok = "LAW HOLDS" if best == pred.get(a, 0) else (
            "BELOW PRED" if best < pred.get(a, 0) else "EXCEEDS PRED — DEVIATION")
        print(f"  a={a}: observed L_max = {best} ({who}) vs predicted {pred.get(a,0)}"
              f"  [{ok}]", flush=True)


def main():
    rng = random.Random(390)
    # (16,4): towers (m,r) with (r-2)m < 4, rm in range
    run(16, 4, 12289, [(1, 5), (2, 3), (4, 2)], [6, 7, 8], rng)
    # (32,3): towers with (r-2)m < 3
    p32 = 12289 if (12289 - 1) % 32 == 0 else 65537 if (65537 - 1) % 32 == 0 else None
    run(32, 3, p32, [(2, 3), (4, 2)], [6, 7, 8], rng)
    return 0


if __name__ == "__main__":
    sys.exit(main())
