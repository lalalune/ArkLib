#!/usr/bin/env python3
"""Probe (#389): the subset-sum fibre law for sub-Johnson single-word lists.

Conjecture: L_max(a) for smooth-domain RS = max subset-sum fibre N_fib(s,r) over
admissible towers, attained by ladder words w = x^{rm} + lambda*x^{(r-1)m}.

Test at (n,k) = (16,3), s=8, m=2, r=3 (rm = 6 >= a), p in {12289, 65537}:
exact list sizes via k-subset interpolation enumeration; candidates = ladder words
at ALL fibre-relevant lambdas (= -sum of triples), monomials, far-generic, hill-climb.
"""
import itertools, random, sys

N, K = 16, 3


def find_g(p, n):
    for h in range(2, 500):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x


def list_size(w, a, xs, p):
    """#codewords (deg<k) with agreement >= a with w, via k-subset interpolants."""
    seen = set()
    best = 0
    for T in itertools.combinations(range(N), K):
        pts = [xs[i] for i in T]
        vals = [w[i] for i in T]
        # Lagrange interpolant evaluated on all nodes
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
        agr = sum(1 for i in range(N) if cw[i] == w[i])
        if agr >= a:
            key = tuple(cw)
            if key not in seen:
                seen.add(key)
        best = max(best, agr)
    return len(seen), best


def main():
    rng = random.Random(389)
    for p in (12289, 65537):
        g = find_g(p, N)
        xs = [pow(g, i, p) for i in range(N)]
        mu8 = sorted({pow(x, 2, p) for x in xs})  # the m=2 power subgroup, order 8
        # subset-sum fibres of mu8, r=3
        from collections import Counter
        fib = Counter()
        for T in itertools.combinations(mu8, 3):
            fib[sum(T) % p] += 1
        nfib = fib.most_common(1)[0]
        print(f"\n==== p={p}: N_fib(8,3) = {nfib[1]} at sum {nfib[0]} "
              f"(distinct sums {len(fib)}/56) ====", flush=True)
        a = 6  # the rm agreement
        rows = []
        # ladder words at the top-5 fibre lambdas
        for sm, cnt in fib.most_common(5):
            lam = (-sm) % p
            w = [(pow(xs[i], 6, p) + lam * pow(xs[i], 4, p)) % p for i in range(N)]
            L, mx = list_size(w, a, xs, p)
            rows.append((f"ladder lam=-{sm} (fib {cnt})", L, mx))
        # monomial words
        for j in (6, 7, 5):
            w = [pow(xs[i], j, p) for i in range(N)]
            L, mx = list_size(w, a, xs, p)
            rows.append((f"x^{j}", L, mx))
        # far-generic
        for t in range(3):
            w = [rng.randrange(p) for _ in range(N)]
            L, mx = list_size(w, a, xs, p)
            rows.append((f"generic#{t}", L, mx))
        # hill-climb on list size
        best_hc = 0
        for restart in range(4):
            w = [(pow(xs[i], 6, p) + ((-nfib[0]) % p) * pow(xs[i], 4, p)) % p
                 for i in range(N)] if restart < 2 else [rng.randrange(p) for _ in range(N)]
            cur, _ = list_size(w, a, xs, p)
            for _ in range(60):
                i, v = rng.randrange(N), rng.randrange(p)
                old = w[i]; w[i] = v
                L2, _ = list_size(w, a, xs, p)
                if L2 >= cur: cur = L2
                else: w[i] = old
            best_hc = max(best_hc, cur)
        rows.append(("hill-climb max", best_hc, '-'))
        print(f"{'word':>24} | L(a=6) | max-agr")
        for name, L, mx in rows:
            print(f"{name:>24} | {L:>6} | {mx}", flush=True)
        lad_max = max(L for nm, L, _ in rows if nm.startswith('ladder'))
        oth_max = max(L for nm, L, _ in rows if not nm.startswith('ladder')
                      and isinstance(L, int))
        print(f"VERDICT p={p}: ladder max {lad_max} vs N_fib {nfib[1]} vs others {oth_max}"
              f" -> {'LAW HOLDS (ladder=fibre, extremal)' if lad_max == nfib[1] and lad_max >= oth_max else 'DEVIATION - investigate'}",
              flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
