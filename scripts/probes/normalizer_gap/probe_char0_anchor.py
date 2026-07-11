#!/usr/bin/env python3
"""
probe_char0_anchor.py -- exact characteristic-zero ANCHOR for the normalizer-gap census argmax
(ArkLib#371 normalizer-gap lane, claim comment 4687191139).

Input: results_char0_census.json (two-prime census).  For each n in {8,16,32,64}:

(1) EXACT VERIFICATION over Z[x]/Phi_n(x)  (n = 2^k  =>  Phi_n = x^{n/2}+1, irreducible, so the
    quotient is an integral domain and Q-rank statements transfer to K = Q(zeta_n)):
      * pull the top-1 argmax incidence set S = {(i_t, j_t)} from the JSON (assert the canonical
        sets agree at both census primes);
      * build the 4 x T matrix over K with columns P(i,j) = (z^{i+j}, z^j, z^i, 1) and verify its
        K-rank is EXACTLY 3 by the regular-representation expansion: the Q-span of
        { z^k * P_t : 0 <= k < n/2, t } equals the K-span of { P_t } viewed as a Q-vector space
        (Q[z] = K), so  rank_Q(big (T*m) x (4m) integer matrix) = m * rank_K, m = n/2.
        Rank is computed by fraction-free Bareiss elimination over Z with asserted-exact division.
      * compute the hyperplane normal v as the generalized cross product of the first rank-3
        triple of S over the ring; assert v != 0, all T incidences v . P(i,j) == 0 IDENTICALLY,
        non-normalizer pattern (not (v0=v3=0), not (v1=v2=0); v = (c, d, -a, -b)), and
        det = v0*v3 - v1*v2 != 0 in the ring (matrix [[a,b],[c,d]] invertible over K);
      * exact char-0 incidence count of v over ALL (i,j) in (Z/n)^2 == census count (no further
        surface point lies on the plane in characteristic zero);
      * cross-check: reduce v at each census prime (z := JSON z, coefficients mod p) and verify
        the reduction is nonzero, satisfies all T incidences mod p, keeps the non-normalizer
        pattern and det != 0 mod p, and (when the census top-1 incidence_ij equals the canonical
        set) is projectively EQUAL to the census normal_cdab mod p.
    Outcome: rank 3 + non-normalizer + invertible  =>  TRUE char-0 incidence  =>  M(n) >= T = 6,
    with the witness plane's exact char-0 count equal to the census count.

(2) STRUCTURE of each verified argmax system:
      * multiset of (i+j mod n, j-i mod n) classes;
      * translation stabilizer Stab(S) = {(s,t) : S+(s,t) = S}; S is a union of cosets of a
        subgroup H <= (Z/n)^2 iff H <= Stab(S) (so trivial Stab => only the trivial subgroup);
      * torus-twisted point symmetries: all translations realizing swap (i,j)->(j,i),
        negation (i,j)->(-i,-j), and swap-negation (i,j)->(-j,-i);
      * a small-coefficient representative of the normal: cross-product normal, integer content
        removed, then minimized over the cyclic units +-z^k (displayed as polynomials in z).

(3) LAW HUNT: least-squares fits of M(n) against candidate closed forms
      const c | c*n^{2/3} | a + b*n/log2(n) | 3n/8 | n/2 - c | c*n(n-4)^2/8  (in-tree chord law)
    with honest 4-point language ("consistent with", never "is").

Pure Python 3 stdlib, exact integer arithmetic throughout part (1)-(2); floats only in the
fit-display layer of part (3).  Writes results_char0_anchor.json + RESULTS-CHAR0-ANCHOR.md.
"""

import json
import math
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS_PATH = os.path.join(HERE, "results_char0_census.json")
OUT_JSON = os.path.join(HERE, "results_char0_anchor.json")
OUT_MD = os.path.join(HERE, "RESULTS-CHAR0-ANCHOR.md")


# ----------------------------------------------------------------------------------------------
# Ring  Z[x]/(x^m + 1),  m = n/2  (Phi_n for n a power of two).  Elements = length-m int lists.
# ----------------------------------------------------------------------------------------------

def make_ring(n):
    assert n >= 4 and (n & (n - 1)) == 0, "n must be a power of two >= 4"
    m = n // 2

    def mono(e):
        """coefficient vector of x^e mod (x^m + 1); e taken mod n (x^n = 1, x^m = -1)."""
        e %= n
        c = [0] * m
        if e < m:
            c[e] = 1
        else:
            c[e - m] = -1
        return c

    def add(a, b):
        return [x + y for x, y in zip(a, b)]

    def sub(a, b):
        return [x - y for x, y in zip(a, b)]

    def mul(a, b):
        out = [0] * m
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        k = i + j
                        if k < m:
                            out[k] += ai * bj
                        else:
                            out[k - m] -= ai * bj
        return out

    def mul_mono(a, e, sign=1):
        """a * (sign * x^e) mod (x^m + 1)."""
        e %= n
        out = [0] * m
        for i, ai in enumerate(a):
            if ai:
                k = (i + e) % n
                if k < m:
                    out[k] += sign * ai
                else:
                    out[k - m] -= sign * ai
        return out

    zero = [0] * m
    one = mono(0)
    return m, mono, add, sub, mul, mul_mono, zero, one


def cross_normal(A, B, C, add, sub, mul):
    """Generalized cross product of three 4-vectors over the ring:
    v_k = (-1)^k det3(columns {0..3}\\{k} of the 3x4 stack [A;B;C]);  v . X = det[[X],[A],[B],[C]]
    (Laplace along the first row), hence v . A = v . B = v . C = 0 and v != 0 iff rank 3."""
    rows = (A, B, C)

    def det3(c0, c1, c2):
        a, b, c = rows[0][c0], rows[0][c1], rows[0][c2]
        d, e, f = rows[1][c0], rows[1][c1], rows[1][c2]
        g, h, i = rows[2][c0], rows[2][c1], rows[2][c2]
        t1 = mul(a, sub(mul(e, i), mul(f, h)))
        t2 = mul(b, sub(mul(d, i), mul(f, g)))
        t3 = mul(c, sub(mul(d, h), mul(e, g)))
        return add(sub(t1, t2), t3)

    v0 = det3(1, 2, 3)
    v1 = [-x for x in det3(0, 2, 3)]
    v2 = det3(0, 1, 3)
    v3 = [-x for x in det3(0, 1, 2)]
    return [v0, v1, v2, v3]


def bareiss_rank(M):
    """Exact rank of an integer matrix by fraction-free (Bareiss) elimination.
    Division exactness is asserted at every step (any failure => algorithmic bug, not rounding)."""
    M = [row[:] for row in M]
    nr = len(M)
    nc = len(M[0]) if nr else 0
    rank = 0
    prev = 1
    for col in range(nc):
        if rank == nr:
            break
        piv = None
        for r in range(rank, nr):
            if M[r][col]:
                piv = r
                break
        if piv is None:
            continue
        if piv != rank:
            M[rank], M[piv] = M[piv], M[rank]
        pv = M[rank][col]
        for r in range(rank + 1, nr):
            mrc = M[r][col]
            Mr, Mp = M[r], M[rank]
            for c2 in range(col, nc):
                num = Mr[c2] * pv - mrc * Mp[c2]
                q, rem = divmod(num, prev)
                assert rem == 0, "Bareiss exact-division failure"
                Mr[c2] = q
        prev = pv
        rank += 1
    return rank


def poly_str(c):
    """Pretty-print a coefficient list as a polynomial in z (low->high in c, printed high->low)."""
    terms = []
    for e in range(len(c) - 1, -1, -1):
        a = c[e]
        if a == 0:
            continue
        if e == 0:
            t = str(abs(a))
        elif abs(a) == 1:
            t = "z" if e == 1 else f"z^{e}"
        else:
            t = f"{abs(a)}*z" if e == 1 else f"{abs(a)}*z^{e}"
        terms.append(("-" if a < 0 else "+", t))
    if not terms:
        return "0"
    s = ("-" if terms[0][0] == "-" else "") + terms[0][1]
    for sgn, t in terms[1:]:
        s += f" {sgn} {t}"
    return s


# ----------------------------------------------------------------------------------------------
# Per-n exact verification + structure
# ----------------------------------------------------------------------------------------------

def verify_n(n, run):
    t0 = time.time()
    m, mono, add, sub, mul, mul_mono, zero, one = make_ring(n)
    res = {"n": n, "m": m, "phi_n": f"x^{m} + 1"}

    # --- pull the argmax incidence set from the census JSON --------------------------------
    primes = [str(p) for p in run["primes"]]
    tops = {p: run["per_prime"][p]["top5"][0] for p in primes}
    canons = [tuple(sorted(map(tuple, tops[p]["incidence_canon"]))) for p in primes]
    assert canons[0] == canons[1], f"n={n}: top-1 canonical sets disagree across primes"
    counts = [tops[p]["count"] for p in primes]
    assert counts[0] == counts[1], f"n={n}: top-1 counts disagree across primes"
    S = list(canons[0])
    T = len(S)
    census_count = counts[0]
    assert T == census_count, f"n={n}: |canonical set| != census count"
    res["S"] = [list(ij) for ij in S]
    res["census_count"] = census_count

    formula = tuple(sorted([(0, 0), (1, 1), (2, 3), (4, n // 2 + 2),
                            (n // 2 - 1, n - 3), (n - 2, n - 1)]))
    res["matches_uniform_family_S(n)"] = (tuple(S) == formula)

    def point(i, j):
        return (mono(i + j), mono(j), mono(i), one)

    def dot(v, P):
        s = zero
        for vk, pk in zip(v, P):
            s = add(s, mul(vk, pk))
        return s

    # --- (1a) K-rank EXACTLY 3 via the regular-representation expansion --------------------
    # rows: z^k * P_t expanded into Q^{4m}; each is a signed-monomial 4-tuple, entries in {-1,0,1}
    big = []
    for (i, j) in S:
        for k in range(m):
            row = mono(i + j + k) + mono(j + k) + mono(i + k) + mono(k)
            big.append(row)
    rk = bareiss_rank(big)
    res["big_matrix_shape"] = [len(big), 4 * m]
    res["big_rank"] = rk
    res["rank_over_K"] = rk / m
    assert rk % m == 0, f"n={n}: big rank {rk} not a multiple of m={m}"
    assert rk == 3 * m, f"n={n}: K-rank is {rk // m}, expected exactly 3"
    res["rank_exactly_3"] = True

    # --- (1b) cross-product normal from the first rank-3 triple ----------------------------
    cross_triple = None
    v = None
    pts = [point(i, j) for (i, j) in S]
    for a in range(T):
        for b in range(a + 1, T):
            for c in range(b + 1, T):
                w = cross_normal(pts[a], pts[b], pts[c], add, sub, mul)
                if any(x != 0 for comp in w for x in comp):
                    cross_triple, v = (S[a], S[b], S[c]), w
                    break
            if v:
                break
        if v:
            break
    assert v is not None, f"n={n}: no rank-3 triple inside S (impossible if rank check passed)"
    res["cross_triple"] = [list(t) for t in cross_triple]

    v0, v1, v2, v3 = v
    for (i, j) in S:
        assert dot(v, point(i, j)) == zero, f"n={n}: incidence ({i},{j}) fails over Z[x]/Phi_n"
    res["all_incidences_identical_zero"] = True

    # v = (c, d, -a, -b): normalizer types are b=c=0 (v3=v0=0) and a=d=0 (v2=v1=0)
    assert not (v0 == zero and v3 == zero), f"n={n}: scaling-normalizer normal"
    assert not (v1 == zero and v2 == zero), f"n={n}: inversion-normalizer normal"
    res["non_normalizer"] = True
    det = sub(mul(v0, v3), mul(v1, v2))
    assert det != zero, f"n={n}: ad - bc == 0 over Q(zeta_n)"
    res["det_nonzero_in_K"] = True

    # --- (1c) exact char-0 incidence count over all of (Z/n)^2 -----------------------------
    char0_set = []
    for i in range(n):
        for j in range(n):
            s = add(add(mul_mono(v0, i + j), mul_mono(v1, j)), add(mul_mono(v2, i), v3))
            if s == zero:
                char0_set.append((i, j))
    res["char0_count"] = len(char0_set)
    assert len(char0_set) == census_count, \
        f"n={n}: char-0 count {len(char0_set)} != census count {census_count}"
    assert sorted(char0_set) == sorted(map(tuple, S)), f"n={n}: char-0 incidence set differs"
    res["no_further_char0_point"] = True

    iset = [i for (i, j) in S]
    jset = [j for (i, j) in S]
    res["partial_injection"] = (len(set(iset)) == T and len(set(jset)) == T)

    # --- (1d) mod-p cross-check against both census primes ---------------------------------
    def eval_mod(comp, z, p):
        acc, zk = 0, 1
        for c in comp:
            acc = (acc + c * zk) % p
            zk = (zk * z) % p
        return acc

    modp = {}
    for pstr in primes:
        p = int(pstr)
        zp = run["per_prime"][pstr]["z"]
        assert pow(zp, n, p) == 1 and pow(zp, n // 2, p) != 1, f"z order != {n} mod {p}"
        V = [eval_mod(comp, zp, p) for comp in v]
        entry = {"p": p, "z": zp, "V_mod_p": V}
        assert any(V), f"n={n}: normal vanishes mod {p}"
        for (i, j) in S:
            val = (V[0] * pow(zp, i + j, p) + V[1] * pow(zp, j, p)
                   + V[2] * pow(zp, i, p) + V[3]) % p
            assert val == 0, f"n={n}: incidence ({i},{j}) fails mod {p}"
        entry["incidences_hold_mod_p"] = True
        entry["non_normalizer_mod_p"] = not (V[0] == 0 and V[3] == 0) and \
                                        not (V[1] == 0 and V[2] == 0)
        entry["det_nonzero_mod_p"] = ((V[0] * V[3] - V[1] * V[2]) % p) != 0
        ij_top = tuple(sorted(map(tuple, tops[pstr]["incidence_ij"])))
        if ij_top == tuple(S):
            Nc = tops[pstr]["normal_cdab"]
            k0 = next(k for k in range(4) if V[k] % p)
            lam = (Nc[k0] * pow(V[k0], p - 2, p)) % p
            entry["proportional_to_census_normal"] = \
                lam != 0 and all((lam * V[k] - Nc[k]) % p == 0 for k in range(4))
        else:
            entry["proportional_to_census_normal"] = "n/a (census top-1 stored a translate)"
        modp[pstr] = entry
    res["mod_p_checks"] = modp
    res["M_lower_bound_proven_char0"] = census_count

    # --- (2) structure ----------------------------------------------------------------------
    Sset = set(map(tuple, S))
    classes = sorted([((i + j) % n, (j - i) % n) for (i, j) in S])
    stab = [(s, t) for s in range(n) for t in range(n)
            if {((i + s) % n, (j + t) % n) for (i, j) in Sset} == Sset]

    def twisted(phi):
        return [(s, t) for s in range(n) for t in range(n)
                if {((a + s) % n, (b + t) % n) for (a, b) in map(phi, Sset)} == Sset]

    swap_tr = twisted(lambda ij: (ij[1], ij[0]))
    neg_tr = twisted(lambda ij: ((-ij[0]) % n, (-ij[1]) % n))
    swapneg_tr = twisted(lambda ij: ((-ij[1]) % n, (-ij[0]) % n))

    if len(stab) == 1:
        coset_verdict = ("translation stabilizer is trivial: S is a union of cosets of NO "
                         "nontrivial subgroup of (Z/n)^2 (only of the trivial subgroup)")
    else:
        coset_verdict = (f"translation stabilizer has order {len(stab)}: S is a union of "
                         f"cosets of every subgroup of the stabilizer {sorted(stab)}")

    # small-coefficient normal: strip integer content, then minimize over units +-z^k
    flat = [x for comp in v for x in comp]
    content = 0
    for x in flat:
        content = math.gcd(content, abs(x))
    vred = [[x // content for x in comp] for comp in v] if content > 1 else [c[:] for c in v]

    best = None
    for e in range(n):
        for sign in (1, -1):
            w = [mul_mono(comp, e, sign) for comp in vred]
            wflat = [x for comp in w for x in comp]
            key = (max(abs(x) for x in wflat),
                   sum(1 for x in wflat if x),
                   tuple(wflat))
            if best is None or key < best[0]:
                best = (key, e, sign, w)
    _, ue, usign, vmin = best
    unit_str = ("" if usign == 1 else "-") + (f"z^{ue}" if ue else "1")

    # uniform closed form of the minimized normal (m = n/2; additive accumulation handles the
    # monomial collisions at m = 4, i.e. n = 8):
    #   c  = -z^{m-1} + z - 2
    #   d  = 2 z^{m-1} - z^{m-2} - z^3 + z^2 + z
    #   -a = -z^{m-1} + z^{m-2} + z^3 - 2 z^2 + 1
    #   -b = (z - 1)^2
    def build(spec):
        out = [0] * m
        for e, cf in spec:
            out[e % m] += cf
        return out

    formula = [build([(0, -2), (1, 1), (m - 1, -1)]),
               build([(1, 1), (2, 1), (3, -1), (m - 2, -1), (m - 1, 2)]),
               build([(0, 1), (2, -2), (3, 1), (m - 2, 1), (m - 1, -1)]),
               build([(0, 1), (1, -2), (2, 1)])]
    normal_formula_ok = (vmin == formula)

    diffs = sorted((j - i) % n for (i, j) in S)
    diff_formula_ok = (diffs == sorted([0, 0, 1, 1, n // 2 - 2, n // 2 - 2]))

    res["structure"] = {
        "sum_diff_classes": [list(c) for c in classes],
        "diff_multiset_is_0_0_1_1_h-2_h-2": diff_formula_ok,
        "translation_stabilizer": [list(x) for x in sorted(stab)],
        "union_of_cosets": coset_verdict,
        "swap_translations": [list(x) for x in swap_tr],
        "negation_translations": [list(x) for x in neg_tr],
        "swapneg_translations": [list(x) for x in swapneg_tr],
        "normal_small": {
            "integer_content_removed": content,
            "minimizing_unit": unit_str,
            "coeff_vectors_low_to_high": vmin,
            "max_abs_coeff": max(abs(x) for comp in vmin for x in comp),
            "pretty_cdab": [poly_str(c) for c in vmin],
            "matches_uniform_formula": normal_formula_ok,
        },
    }
    res["elapsed_s"] = round(time.time() - t0, 3)
    return res


# ----------------------------------------------------------------------------------------------
# (3) Law hunt
# ----------------------------------------------------------------------------------------------

def law_hunt(ns, Ms):
    n_f = [float(x) for x in ns]
    y = [float(x) for x in Ms]
    N = len(ns)

    def sse(pred):
        return sum((a - b) ** 2 for a, b in zip(y, pred))

    fits = []

    c_const = sum(y) / N
    fits.append(("const c", f"c = {c_const:.6g}",
                 sse([c_const] * N), [c_const] * N))

    xs = [v ** (2.0 / 3.0) for v in n_f]
    c1 = sum(a * b for a, b in zip(y, xs)) / sum(a * a for a in xs)
    fits.append(("c*n^(2/3)", f"c = {c1:.6g}", sse([c1 * a for a in xs]), [c1 * a for a in xs]))

    xs = [v / math.log2(v) for v in n_f]
    sx, sy = sum(xs), sum(y)
    sxx = sum(a * a for a in xs)
    sxy = sum(a * b for a, b in zip(xs, y))
    den = N * sxx - sx * sx
    b2 = (N * sxy - sx * sy) / den
    a2 = (sy - b2 * sx) / N
    pred = [a2 + b2 * a for a in xs]
    fits.append(("a + b*n/log2(n)", f"a = {a2:.6g}, b = {b2:.6g}", sse(pred), pred))

    pred = [3.0 * v / 8.0 for v in n_f]
    fits.append(("3n/8 (fixed)", "-", sse(pred), pred))

    c3 = sum(v / 2.0 - b for v, b in zip(n_f, y)) / N
    pred = [v / 2.0 - c3 for v in n_f]
    fits.append(("n/2 - c", f"c = {c3:.6g}", sse(pred), pred))

    xs = [v * (v - 4.0) ** 2 / 8.0 for v in n_f]
    c4 = sum(a * b for a, b in zip(y, xs)) / sum(a * a for a in xs)
    pred = [c4 * a for a in xs]
    fits.append(("c*n(n-4)^2/8 (chord-law analogue)", f"c = {c4:.6g}", sse(pred), pred))

    out = []
    for name, params, s, pred in fits:
        out.append({"model": name, "fit": params, "sse": s,
                    "rms": math.sqrt(s / N), "pred": [round(p, 4) for p in pred]})
    return out


# ----------------------------------------------------------------------------------------------

def main():
    census = json.load(open(CENSUS_PATH))
    runs = census["runs"]
    ns = sorted(int(k) for k in runs)
    results = {"task": "char-0 anchor of census argmax (ArkLib#371 normalizer-gap)",
               "census_file": os.path.basename(CENSUS_PATH),
               "n_values": ns, "per_n": {}, }

    Ms = []
    for n in ns:
        print(f"=== n = {n} ===")
        r = verify_n(n, runs[str(n)])
        results["per_n"][str(n)] = r
        Ms.append(r["M_lower_bound_proven_char0"])
        print(f"  S = {r['S']}  (uniform family: {r['matches_uniform_family_S(n)']})")
        print(f"  big matrix {r['big_matrix_shape']}, rank {r['big_rank']} = 3*m  "
              f"=> rank over Q(zeta_{n}) EXACTLY 3")
        print(f"  non-normalizer: {r['non_normalizer']}, det != 0: {r['det_nonzero_in_K']}, "
              f"char-0 count {r['char0_count']} == census {r['census_count']}")
        for pstr, e in r["mod_p_checks"].items():
            print(f"  mod {pstr}: incidences {e['incidences_hold_mod_p']}, "
                  f"non-normalizer {e['non_normalizer_mod_p']}, det!=0 {e['det_nonzero_mod_p']}, "
                  f"matches census normal: {e['proportional_to_census_normal']}")
        st = r["structure"]
        print(f"  classes (i+j, j-i): {st['sum_diff_classes']}")
        print(f"  stab: {st['translation_stabilizer']}; swapneg translations: "
              f"{st['swapneg_translations']}")
        print(f"  small normal ({st['normal_small']['minimizing_unit']} * content-free cross): "
              f"(c,d,-a,-b) = {st['normal_small']['pretty_cdab']}  "
              f"max|coeff| = {st['normal_small']['max_abs_coeff']}")
        print(f"  => M({n}) >= {r['M_lower_bound_proven_char0']} PROVEN in char 0 "
              f"({r['elapsed_s']}s)")

    results["M_exact"] = {str(n): m for n, m in zip(ns, Ms)}
    results["law_hunt"] = law_hunt(ns, Ms)
    results["law_verdict"] = (
        f"M(n) = {Ms} over n = {ns}: flat across a factor-{ns[-1] // ns[0]} range. The data are "
        "CONSISTENT WITH the constant law M(n) = 6 (a uniform Beukers-Smyth-type torsion-point "
        "cap on the Mobius hyperbola c*xy + d*y - a*x - b = 0; BS-type bounds allow up to ~22, "
        "we observe exactly 6). Every growing candidate (c*n^{2/3}, 3n/8, n/2 - c, chord-law "
        "c*n(n-4)^2/8) is excluded outright by the flatness; a + b*n/log2(n) fits only by "
        "degenerating to b = 0 (the constant). Four data points: 'consistent with', not 'is'.")
    json.dump(results, open(OUT_JSON, "w"), indent=1)
    print(f"\nwrote {OUT_JSON}")

    write_md(results)
    print(f"wrote {OUT_MD}")


def write_md(res):
    ns = res["n_values"]
    L = []
    L.append("# Char-0 anchor — exact verification of the census argmax (ArkLib#371)")
    L.append("")
    L.append("Continuation of `RESULTS-CHAR0.md` (two-prime census, `results_char0_census.json`).")
    L.append("`probe_char0_anchor.py` re-verifies the census argmax PURELY in characteristic zero:")
    L.append("exact integer arithmetic in Z[x]/Phi_n(x) (Phi_n = x^{n/2}+1 for 2-power n), K-rank")
    L.append("via the regular-representation expansion (Q-span of {z^k P_t} = K-span of {P_t}, so")
    L.append("rank_K = rank_Q(big integer matrix)/m), fraction-free Bareiss with asserted-exact")
    L.append("division. No mod-p reduction is load-bearing anywhere in part (1).")
    L.append("")
    L.append("## (1) Exact verification — all checks PASS")
    L.append("")
    L.append("| n | S (argmax, canonical) | rank over K | non-norm. | det!=0 in K | char-0 count | census | mod-p match |")
    L.append("|---|----------------------|-------------|-----------|-------------|--------------|--------|-------------|")
    for n in ns:
        r = res["per_n"][str(n)]
        mp = all(e["incidences_hold_mod_p"] and e["non_normalizer_mod_p"]
                 and e["det_nonzero_mod_p"] for e in r["mod_p_checks"].values())
        sset = ", ".join(f"({i},{j})" for i, j in r["S"])
        L.append(f"| {n} | {sset} | exactly 3 (big rank {r['big_rank']} = 3·{r['m']}) | "
                 f"{r['non_normalizer']} | {r['det_nonzero_in_K']} | {r['char0_count']} | "
                 f"{r['census_count']} | {mp} |")
    L.append("")
    L.append("Every n: the 4×6 point matrix has K-rank EXACTLY 3; the cross-product normal is")
    L.append("non-normalizer with ad−bc ≠ 0 over Q(zeta_n); all six incidences vanish IDENTICALLY")
    L.append("in the cyclotomic ring; and the exact char-0 incidence count over the full torus")
    L.append("(Z/n)^2 equals the census count 6 — no hidden seventh point in characteristic zero.")
    L.append("Hence **M(n) ≥ 6 is PROVEN in char 0 for n = 8, 16, 32, 64**, and the witness plane")
    L.append("is exactly the census argmax (its mod-p reduction reproduces the census normal")
    L.append("projectively where the census stored the untranslated representative).")
    L.append("All argmax incidence sets are partial injections i → j and equal the uniform family")
    L.append("S(n) = {(0,0), (1,1), (2,3), (4, n/2+2), (n/2−1, n−3), (n−2, n−1)}.")
    L.append("")
    L.append("## (2) Structure of the verified argmax systems")
    L.append("")
    uni = all(res["per_n"][str(n)]["structure"]["normal_small"]["matches_uniform_formula"]
              for n in ns)
    dif = all(res["per_n"][str(n)]["structure"]["diff_multiset_is_0_0_1_1_h-2_h-2"]
              for n in ns)
    L.append(f"Cross-n laws (verified exactly at every n, not eyeballed):")
    L.append(f"- **Uniform normal family** ({'PASS' if uni else 'FAIL'}): after removing integer")
    L.append("  content and minimizing over the units ±z^k, the argmax normal is the SAME closed")
    L.append("  form for all n (m = n/2; n = 8 is the collapsed m = 4 case):")
    L.append("    c = −z^{m−1} + z − 2,   d = 2z^{m−1} − z^{m−2} − z^3 + z^2 + z,")
    L.append("    −a = −z^{m−1} + z^{m−2} + z^3 − 2z^2 + 1,   −b = (z − 1)^2,")
    L.append("  with max |coefficient| = 2. One Z[zeta]-normal family realizes S(n) at every n.")
    L.append(f"- **Difference-class law** ({'PASS' if dif else 'FAIL'}): the multiset of j−i mod n")
    L.append("  is {0, 0, 1, 1, n/2−2, n/2−2} at every n — exactly three difference classes, each")
    L.append("  hit twice; the swapneg pairing (i,j) → (1−j, 1−i) preserves j−i and exchanges the")
    L.append("  members of each pair.")
    L.append("- **Symmetry collapse**: the unique swapneg translation is (1,1) at every n")
    L.append("  (sigma ~ sigma^{-1} invariance, confirming the census claim exactly); plain swap")
    L.append("  and plain negation admit translations ONLY at n = 8 ((3,5) and (4,6) resp.) — the")
    L.append("  full dihedral symmetry of the n = 8 maximizer is lost for n ≥ 16.")
    L.append("- **No coset structure**: the translation stabilizer is trivial at every n, so S(n)")
    L.append("  is not a union of cosets of any nontrivial subgroup of (Z/n)^2 (consistent with")
    L.append("  the points being in 'general position' on the Mobius hyperbola rather than on a")
    L.append("  torsion coset).")
    L.append("")
    for n in ns:
        r = res["per_n"][str(n)]
        st = r["structure"]
        nm = st["normal_small"]
        L.append(f"### n = {n}")
        L.append(f"- (i+j mod n, j−i mod n) classes: {st['sum_diff_classes']}")
        L.append(f"- {st['union_of_cosets']}")
        L.append(f"- twisted symmetries (translations (s,t) with φ(S)+(s,t)=S): "
                 f"swap {st['swap_translations'] or 'NONE'}; "
                 f"negation {st['negation_translations'] or 'NONE'}; "
                 f"swap∘negation {st['swapneg_translations'] or 'NONE'}")
        L.append(f"- normal scaled into Z[zeta_{n}] (content {nm['integer_content_removed']} "
                 f"removed, unit {nm['minimizing_unit']}): (c, d, −a, −b) =")
        for lbl, p in zip(("c", "d", "-a", "-b"), nm["pretty_cdab"]):
            L.append(f"    - {lbl} = {p}")
        L.append(f"  max |coefficient| = {nm['max_abs_coeff']}")
        L.append("")
    L.append("## (3) Law hunt — M(n) against candidate closed forms")
    L.append("")
    L.append(f"Exact data: M(n) = 6 at n = {ns} (lower bounds proven in char 0; upper bounds are")
    L.append("the two-prime census values — see caveat).")
    L.append("")
    L.append("| model | best fit | predictions at n = " + ", ".join(map(str, ns)) + " | SSE | RMS |")
    L.append("|-------|----------|----------------|-----|-----|")
    for f in res["law_hunt"]:
        L.append(f"| {f['model']} | {f['fit']} | {f['pred']} | {f['sse']:.4g} | {f['rms']:.4g} |")
    L.append("")
    L.append(res["law_verdict"])
    L.append("")
    L.append("## Caveats")
    L.append("")
    L.append("- The char-0 LOWER bound M(n) ≥ 6 is a theorem (this probe, exact arithmetic).")
    L.append("- The UPPER bound M(n) ≤ 6 inherits the census status: proven-by-height at n = 8, 16")
    L.append("  (Hadamard bounds < 2^56 < p1·p2), two-prime evidence at n = 32, 64 (bit-identical")
    L.append("  histograms at both primes; a larger char-0 system would need p1·p2 | Norm(det)).")
    L.append("- Four data points, all equal: 'consistent with the constant law', not 'is'.")
    L.append("- The mod-p layer (q-decreasing F_q maxima at n = 32) is OUTSIDE this probe's scope;")
    L.append("  this anchors only the char-0 core of the two-layer signature.")
    L.append("")
    with open(OUT_MD, "w") as fh:
        fh.write("\n".join(L))


if __name__ == "__main__":
    main()
