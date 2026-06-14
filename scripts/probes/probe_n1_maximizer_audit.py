#!/usr/bin/env python3
"""probe_n1_maximizer_audit.py — N1 structured-extremality audit (#357).

Hypothesis N1: the sup in eps_mca over stacks is attained (up to poly slack) on
ORBIT-STRUCTURED pairs. Falsifier: an exact maximizer orbit with no structure.

Method: enumerate stacks (u0, u1) over RS[F_p, <g>, k] *in the codeword-translation
quotient* (syndrome reduction: each coset has a unique representative vanishing on the
first k positions — puncturing is bijective for MDS codes; bad count is translation-
invariant, per the sibling lane's Lean equivariance laws). Compute exact bad-gamma
counts (agreement-set reduction; joint clause antitone in S so testing maximal
agreement sets is complete). Collect maximizers; quotient by the residual equivariance
group (unit scalings a,b; shear s [gamma -> gamma-s]; domain rotation, re-reduced).
Report orbits + structure of representatives.

Verdict semantics: few orbits, all structured -> N1 SUPPORTED at this scale;
any unstructured orbit representative -> N1 REFUTED-at-toy (keep the witness).
"""

import itertools
import sys


def run(p, n, k, min_size, gpow):
    dom = [pow(gpow, i, p) for i in range(n)]
    assert len(set(dom)) == n, "gpow must have order n"
    cws = sorted(set(tuple(sum(c * pow(x, e, p) for e, c in enumerate(coeffs)) % p
                           for x in dom)
                     for coeffs in itertools.product(range(p), repeat=k)))

    # interpolation table for reduction: codeword through values (y0,...,y_{k-1})
    # at dom[0..k-1]
    interp = {}
    for cw in cws:
        interp[tuple(cw[:k])] = cw

    def reduce_w(w):
        cw = interp[tuple(w[:k])]
        return tuple((w[i] - cw[i]) % p for i in range(n))

    # representatives: words vanishing on first k positions
    reps = [(0,) * k + tail for tail in itertools.product(range(p), repeat=n - k)]
    repset = set(reps)
    assert all(reduce_w(w) in repset for w in reps)

    # agreement machinery
    def agree_masks(w):
        out = set()
        for cw in cws:
            m = 0
            for i in range(n):
                if w[i] == cw[i]:
                    m |= 1 << i
            out.add(m)
        return out

    am_cache = {}

    def get_am(w):
        if w not in am_cache:
            am_cache[w] = agree_masks(w)
        return am_cache[w]

    def extendable(w, A):
        return any((A & am) == A for am in get_am(w))

    popcnt = [bin(m).count('1') for m in range(1 << n)]

    def bad_count(w0, w1):
        cnt = 0
        for g in range(p):
            line = tuple((w0[i] + g * w1[i]) % p for i in range(n))
            for am in get_am(line):
                if popcnt[am] < min_size:
                    continue
                if extendable(w0, am) and extendable(w1, am):
                    continue
                cnt += 1
                break
        return cnt

    best = 0
    maxers = []
    for w0 in reps:
        for w1 in reps:
            c = bad_count(w0, w1)
            if c > best:
                best = c
                maxers = [(w0, w1)]
            elif c == best:
                maxers.append((w0, w1))

    # residual group: scalings (a, b), shear s, rotation r (re-reduced)
    rot_perm = [(i + 1) % n for i in range(n)]  # x -> g*x sends dom[i] to dom[i+1]

    def act(w0, w1, a, b, s, r):
        if r:
            w0 = tuple(w0[rot_perm[i]] for i in range(n))
            w1 = tuple(w1[rot_perm[i]] for i in range(n))
        w1n = tuple(b * w1[i] % p for i in range(n))
        w0n = tuple((a * w0[i] + s * w1n[i]) % p for i in range(n))
        return (reduce_w(w0n), reduce_w(w1n))

    maxset = set(maxers)
    seen = set()
    orbits = []
    units = list(range(1, p))
    for m in maxers:
        if m in seen:
            continue
        orb = {m}
        frontier = [m]
        while frontier:
            v0, v1 = frontier.pop()
            for a in units:
                for b in units:
                    for s in range(p):
                        for r in (False, True):
                            nxt = act(v0, v1, a, b, s, r)
                            if nxt in maxset and nxt not in orb:
                                orb.add(nxt)
                                frontier.append(nxt)
        seen |= orb
        orbits.append(orb)

    print(f"p={p} n={n} k={k} |S|>={min_size}: max bad-count={best}, "
          f"#maximizer cosets={len(maxers)}, #orbits={len(orbits)}")
    for oi, orb in enumerate(sorted(orbits, key=len, reverse=True)[:8]):
        rep = min(orb)
        w0, w1 = rep
        supp0 = [i for i in range(n) if w0[i] != 0]
        supp1 = [i for i in range(n) if w1[i] != 0]
        struct = "indicator" if (len(supp0) <= n - k - 1 or len(supp1) <= n - k - 1) \
            else "DENSE"
        print(f"  orbit {oi}: size={len(orb)} rep u0={w0} u1={w1} "
              f"supports=({supp0},{supp1}) [{struct}]")
    if len(orbits) > 8:
        print(f"  ... {len(orbits) - 8} more orbits")
    return best, len(maxers), len(orbits)


def main():
    print("N1 maximizer audit (codeword-coset quotient; residual group = "
          "scalings x shear x rotation)")
    run(5, 4, 2, 3, 2)    # RS[F5,<2>,2] at delta=1/4 — the exact-pin instance
    run(13, 4, 2, 3, 5)   # RS[F13,<5>,2] at delta=1/4 — field-drift check
    run(13, 4, 2, 2, 5)   # same, delta=1/2 — above-Johnson contrast
    print("exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
