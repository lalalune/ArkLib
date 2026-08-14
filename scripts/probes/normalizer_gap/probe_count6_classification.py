#!/usr/bin/env python3
"""Classify ALL count-6 (maximal) non-normalizer planes on the mu_n surface.

Constraint-analysis input for the <=6 theorem (the constant-6 law's upper bound,
DISPROOF_LOG O155): the census counted 300 / 1932 / 9420 count-6 planes through
P(0,0) at n = 16 / 32 / 64 — one uniform mechanism can only kill a hypothetical
7th point if the maximal configurations themselves are classifiable. This probe
collects EVERY count-6 plane (single split prime — structure discovery; the
two-prime agreement of the histograms is already on record), canonicalizes its
incidence set up to the symmetries that act on the problem
(torus translations (i,j)->(i+s,j+t); swapneg (i,j)->(c-j,c-i), the sigma~sigma^{-1}
symmetry; full negation (i,j)->(c-i,c-j) composed with translations), and reports
the orbit representatives with their (j-i)-multiset invariants.

Output: RESULTS-COUNT6-CLASSES.md + results_count6_classes.json.
"""

import json
import os
import sys
from collections import Counter, defaultdict
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))


def is_probable_prime(x):
    for w in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % w == 0:
            return x == w
        d, s = x - 1, 0
        while d % 2 == 0:
            d //= 2
            s += 1
        v = pow(w, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def split_prime(n, lo=1 << 28):
    p = lo + 1
    p += (n - (p - 1) % n) % n
    while not is_probable_prime(p):
        p += n
    return p


def order_n_elt(p, n):
    for g in range(2, p):
        z = pow(g, (p - 1) // n, p)
        # exact order n check
        ok = z != 1
        if ok:
            o = 1
            v = z
            while v != 1:
                v = v * z % p
                o += 1
                if o > n:
                    break
            ok = (o == n)
        if ok:
            return z
    raise RuntimeError


def classify(n):
    p = split_prime(n)
    z = order_n_elt(p, n)
    pts = {}
    for i in range(n):
        for j in range(n):
            pts[(i, j)] = (pow(z, (i + j) % n, p), pow(z, j, p), pow(z, i, p), 1)
    P00 = pts[(0, 0)]
    others = [(ij, v) for ij, v in pts.items() if ij != (0, 0)]

    def cross3(A, B, C):
        """Normal of the rank-3 span of rows A,B,C in F_p^4 (4D cross product)."""
        M = [A, B, C]
        out = []
        sign = 1
        for k in range(4):
            sub = [[M[r][c] for c in range(4) if c != k] for r in range(3)]
            det = (sub[0][0] * (sub[1][1] * sub[2][2] - sub[1][2] * sub[2][1])
                   - sub[0][1] * (sub[1][0] * sub[2][2] - sub[1][2] * sub[2][0])
                   + sub[0][2] * (sub[1][0] * sub[2][1] - sub[1][1] * sub[2][0])) % p
            out.append(sign * det % p)
            sign = -sign
        return tuple(out)

    seen = {}
    pt_list = list(pts.items())
    for (ij1, v1), (ij2, v2) in combinations(others, 2):
        nrm = cross3(P00, v1, v2)
        if all(c == 0 for c in nrm):
            continue
        fz = next(c for c in nrm if c)
        inv = pow(fz, p - 2, p)
        key = tuple(c * inv % p for c in nrm)
        if key in seen:
            continue
        # normal coords order: (c, d, -a, -b) against (z^{i+j}, z^j, z^i, 1)
        cc, dd, na, nb = key
        a, b = (-na) % p, (-nb) % p
        if (b == 0 and cc == 0) or (a == 0 and dd == 0):
            seen[key] = None  # normalizer type
            continue
        if (a * dd - b * cc) % p == 0:
            seen[key] = None  # singular
            continue
        inc = tuple(sorted(ij for ij, v in pt_list
                           if (key[0] * v[0] + key[1] * v[1] + key[2] * v[2]
                               + key[3]) % p == 0))
        seen[key] = inc
    count6 = [inc for inc in seen.values() if inc and len(inc) == 6]
    print(f"[n={n}] p={p}: {len(count6)} count-6 planes through P00",
          file=sys.stderr)

    # canonicalize up to: translations x swapneg x negation
    def variants(S):
        out = []
        base = list(S)
        for (form) in range(3):
            if form == 0:
                T = base                                      # identity
            elif form == 1:
                T = [(-j % n, -i % n) for (i, j) in base]     # swapneg core
            else:
                T = [(-i % n, -j % n) for (i, j) in base]     # negation core
            for (s, t) in [(-T[0][0] % n, 0)]:                # anchor first to i=0
                pass
            # full translation orbit canonical form: min over all translations
            best = None
            for (s, t) in set(((-i) % n, (-j) % n) for (i, j) in T):
                U = tuple(sorted(((i + s) % n, (j + t) % n) for (i, j) in T))
                if best is None or U < best:
                    best = U
            out.append(best)
        return min(out)

    classes = defaultdict(int)
    invariants = {}
    for inc in count6:
        cf = variants(inc)
        classes[cf] += 1
        if cf not in invariants:
            dmul = tuple(sorted(Counter((j - i) % n for (i, j) in cf).items()))
            smul = tuple(sorted(Counter((i + j) % n for (i, j) in cf).items()))
            inj = (len({i for i, _ in cf}) == 6 and len({j for _, j in cf}) == 6)
            invariants[cf] = {"diff_multiset": dmul, "sum_classes": len(smul),
                              "partial_injection": inj}
    return p, len(count6), classes, invariants


def main():
    results = {}
    lines = ["# Count-6 plane classification (single split prime, structure discovery)",
             ""]
    for n in (16, 32):
        p, total, classes, inv = classify(n)
        reps = sorted(classes.items(), key=lambda kv: -kv[1])
        lines.append(f"## n = {n} (p = {p}): {total} count-6 planes "
                     f"-> {len(classes)} symmetry classes")
        for cf, cnt in reps[:12]:
            iv = inv[cf]
            lines.append(f"- x{cnt}: {list(cf)}  diff(j-i)={iv['diff_multiset']}  "
                         f"inj={iv['partial_injection']}")
        if len(reps) > 12:
            lines.append(f"- ... {len(reps) - 12} more classes")
        lines.append("")
        results[n] = {"p": p, "total": total, "n_classes": len(classes),
                      "classes": [{"rep": [list(t) for t in cf], "count": cnt,
                                   **{k: (list(v) if isinstance(v, tuple) else v)
                                      for k, v in inv[cf].items()}}
                                  for cf, cnt in reps]}
    open(os.path.join(HERE, "RESULTS-COUNT6-CLASSES.md"), "w").write(
        "\n".join(lines) + "\n")
    json.dump(results, open(os.path.join(HERE, "results_count6_classes.json"),
                            "w"), indent=1)
    print("\n".join(lines[:30]))


if __name__ == "__main__":
    main()
