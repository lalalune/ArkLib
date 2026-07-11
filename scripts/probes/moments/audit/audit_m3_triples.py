#!/usr/bin/env python3
"""ADVERSARIAL AUDIT brute force for M3 (O133 audit) — independent algorithm.

M3[j1,j2,j3] = sum over ALL q^n received words u of a_{j1}(u)a_{j2}(u)a_{j3}(u)
             = sum over ALL ordered codeword TRIPLES (p1,p2,p3) of
               #{u : agree(p_i, u) = j_i, i = 1,2,3}.

Algorithm (deliberately different from both landed engines):
  * NO translation reduction, NO pencil decomposition, NO weight distribution.
  * Enumerate all q^{3k} ordered codeword triples directly.
  * Per coordinate x the number of u_x realizing an agreement pattern depends
    only on the coincidence pattern of (p1(x), p2(x), p3(x)):
       ALL  (p1=p2=p3)        factor z1z2z3 + (q-1)
       E12  (p1=p2 != p3)     factor z1z2 + z3 + (q-2)
       E13  (p1=p3 != p2)     factor z1z3 + z2 + (q-2)
       E23  (p2=p3 != p1)     factor z2z3 + z1 + (q-2)
       DST  (all distinct)    factor z1 + z2 + z3 + (q-3)
    #{u : agreements = (j1,j2,j3)} = [z1^j1 z2^j2 z3^j3] prod_x factor_x.
  * The product is computed by naive per-coordinate sparse polynomial
    multiplication (a DP over coordinates), NOT closed-form binomials.
  * Triples are bucketed by the bitmask triple (eq(p1,p2), eq(p1,p3), eq(p2,p3))
    over the n coordinates; each bucket's polynomial computed once.

Checks: total M3 mass == q^(n+3k); S3 symmetry; output JSON in the engines'
schema (M1 included via its own direct count from the same buckets is skipped;
M1 compared from the engines' own files separately).
"""
import json
import sys
from itertools import product


def codeword_evals(q, k, domain):
    out = []
    for coeffs in product(range(q), repeat=k):
        # evaluate sum coeffs[e] * x^e via Horner from the top coefficient
        ev = []
        for x in domain:
            acc = 0
            for c in reversed(coeffs):
                acc = (acc * x + c) % q
            ev.append(acc)
        out.append(tuple(ev))
    return out


def poly_mul(P, factor):
    out = {}
    for (a, b, c), v in P.items():
        for (da, db, dc), w in factor.items():
            kk = (a + da, b + db, c + dc)
            out[kk] = out.get(kk, 0) + v * w
    return out


def n_poly_for_masks(q, n, m12, m13, m23):
    ALL = {(1, 1, 1): 1, (0, 0, 0): q - 1}
    E12 = {(1, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): q - 2}
    E13 = {(1, 0, 1): 1, (0, 1, 0): 1, (0, 0, 0): q - 2}
    E23 = {(0, 1, 1): 1, (1, 0, 0): 1, (0, 0, 0): q - 2}
    DST = {(1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): q - 3}
    P = {(0, 0, 0): 1}
    for i in range(n):
        b12 = (m12 >> i) & 1
        b13 = (m13 >> i) & 1
        b23 = (m23 >> i) & 1
        s = b12 + b13 + b23
        assert s != 2, "inconsistent equality pattern"  # transitivity
        if s == 3:
            f = ALL
        elif b12:
            f = E12
        elif b13:
            f = E13
        elif b23:
            f = E23
        else:
            f = DST
        P = poly_mul(P, f)
    return P


def main():
    q = int(sys.argv[1])
    k = int(sys.argv[2])
    domain = sorted(int(t) % q for t in sys.argv[3].split(","))
    assert all(domain) and len(set(domain)) == len(domain)
    n = len(domain)
    cws = codeword_evals(q, k, domain)
    m = len(cws)
    assert m == q ** k

    # eq bitmasks for every ordered pair
    eq = [[0] * m for _ in range(m)]
    for i in range(m):
        ci = cws[i]
        row = eq[i]
        for j in range(m):
            cj = cws[j]
            mask = 0
            for t in range(n):
                if ci[t] == cj[t]:
                    mask |= 1 << t
            row[j] = mask

    # bucket ordered triples by (m12, m13, m23) into a flat array
    SH = n
    buckets = [0] * (1 << (3 * SH))
    for i in range(m):
        eqi = eq[i]
        for j in range(m):
            base = (eqi[j] << (2 * SH))
            eqj = eq[j]
            for l in range(m):
                buckets[base | (eqi[l] << SH) | eqj[l]] += 1

    M3 = {}
    nonzero = 0
    for key, cnt in enumerate(buckets):
        if not cnt:
            continue
        nonzero += 1
        m23 = key & ((1 << SH) - 1)
        m13 = (key >> SH) & ((1 << SH) - 1)
        m12 = key >> (2 * SH)
        P = n_poly_for_masks(q, n, m12, m13, m23)
        for kk, v in P.items():
            if v:
                M3[kk] = M3.get(kk, 0) + cnt * v

    assert sum(M3.values()) == q ** (n + 3 * k), "total mass != q^(n+3k)"
    for (a, b, c), v in M3.items():
        assert M3.get((b, a, c), 0) == v and M3.get((a, c, b), 0) == v, "not S3-symmetric"

    out = {"q": q, "n": n, "k": k, "domain": domain,
           "M3": {f"{a},{b},{c}": M3[(a, b, c)] for (a, b, c) in sorted(M3) if M3[(a, b, c)]}}
    print(json.dumps(out, separators=(",", ":")))
    print(f"buckets used: {nonzero}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
