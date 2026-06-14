#!/usr/bin/env python3
"""A1 falsify-first: is there ANY coefficient generator violating [Jo26]
interleaving exactness beyond |Omega| <= q?

[Jo26] (ePrint 2026/891) Thm 4.4: a coefficient generator G : Omega -> F_q^l
with |Omega| <= q satisfies eps_G(C^{=s}, delta) = eps_G(C, delta) EXACTLY;
for |Omega| > q only the factor A(q,s) = 1 + 1/q + ... + 1/q^{s-1} is proven
(Thm 4.2).  probe_jo26_multiseed_exactness.py observed ratio == 1.000 for
the STRUCTURED generator (a,b) |-> (1,a,b) at |Omega| = q^2.  Question
(hypothesis A1 of open-math-hypotheses-334-deltastar-2026-06.md): does ANY
generator at all violate equality?

Search plan (s = 2 interleaving throughout; A(q,2) = (q+1)/q):

  Part 1  RS[F_3, n=2, k=1] (smooth domain {1,2} = the multiplicative group
          of F_3; k=1 so codewords are the constants; n-k=1 so words-mod-code
          = syndromes in F_3), l = 2:
            |Omega| = 4: ALL (3^2)^4  =  6561 functions G : Omega -> F_3^2
            |Omega| = 5: ALL (3^2)^5  = 59049 functions (fully exhaustive —
                         fast enough; no normalization/sampling needed)
          Stacks swept exhaustively via the syndrome reduction (adding a
          codeword to any stack word changes no event): base stacks =
          F_3^2 (9), interleaved stacks = (F_3^2)^2 (81).
  Part 2  same code, l = 3, |Omega| = 4: all 27^4 = 531441 functions,
          enumerated EXACTLY via value-multisets (C(30,4) = 27405 classes;
          all bad-seed counts are invariant under permuting Omega, so the
          class sweep IS the exhaustive sweep; invariance additionally
          spot-checked against direct function evaluation).  This exceeds
          the requested "sample 20000 random ones".
  Part 3  (EXTENSION beyond the task spec; generators SAMPLED, stacks
          exhaustive)  RS[F_5, n=4, k=2] (n-k = 2: the first regime with
          nontrivial partial witness sets), l = 2, |Omega| = 6 > q = 5:
          the projective-line generator (the 6 directions of F_5^2 — the
          q+1 lines DO cover F_5^2, exactly the configuration on which the
          covering lemma behind Thm 4.4 fails), random direction multisets,
          scaled variants, and random generators.  Per generator the stack
          sweep is exhaustive and syndrome-reduced: 625 base stacks,
          390625 interleaved stacks, radii m in {3,4}.

For each generator:  base  = max over l-stacks of #bad seeds for C,
                     inter = same for C^{=2}.
Record any generator with inter > base; check the Thm 4.2 transcription
q * inter <= (q+1) * base  everywhere (counts; A(q,2) = (q+1)/q).

Event convention (mcaEventP shape, as in the sibling probes): seed omega is
bad for a stack iff the G(omega)-combination extends from some admissible
witness set S (|S| >= m) that is NOT a joint witness of the whole stack;
for the interleaved code both rows must extend from the SAME S.

Internal cross-checks (all asserted; exit 0 iff factor inequality and all
cross-checks hold):
  * ext_mask validated against brute-force codeword-agreement for BOTH
    instances (every syndrome, every subset, all codewords);
  * fast bitmask path == general syndrome-mask engine (ALL 6561 generators
    at |Omega|=4 l=2; random samples for the other F_3 configs);
  * syndrome engines == an INDEPENDENT WORD-LEVEL engine that never builds
    syndromes (membership by codeword enumeration, all word stacks swept);
  * multiset reduction == direct function evaluation (random permutations);
  * Part 3 numpy engine == pure-python engine on sampled generators.
Any inter > base hit would be re-verified through the independent engine
before being reported as a VIOLATION.

A PRIORI NOTE (found while building this; reported honestly): at n-k = 1
the only admissible radius is m = n (delta = 0), so "close" = "in the
code", the witness set is always the full domain, and the bad-seed set of
an interleaved stack is {omega : G(omega) in W_A cap W_B} for the two
column orthogonal-complement subspaces W_A, W_B <= F_3^l, while every
single subspace W_A is already realized by a base stack (take column B =
0 or = column A).  Since W_A cap W_B <= W_A, inter <= base is FORCED for
every generator on ANY n-k = 1 instance: the requested exhaustive sweep
can only confirm equality.  That is why Part 3 (n-k = 2: bad-seed sets
are UNIONS of subspaces over witness sets, and a covering configuration
is geometrically possible) is included as the real falsification attempt.
"""

from itertools import product, combinations, combinations_with_replacement
import math
import random
import sys

# ---- shared linear algebra (as in probe_jo26_multiseed_exactness.py) ----


def rref(mat, p):
    m = [row[:] for row in mat]
    rows, cols = len(m), len(m[0]) if m else 0
    piv = []
    r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p != 0), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        inv = pow(m[r][c], p - 2, p)
        m[r] = [(x * inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p != 0:
                f = m[i][c]
                m[i] = [(a - f * b) % p for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return m[:r], piv


def nullspace(mat, p):
    red, piv = rref(mat, p)
    cols = len(mat[0])
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * cols
        v[f] = 1
        for r, c in enumerate(piv):
            v[c] = (-red[r][f]) % p
        basis.append(v)
    return basis


def solve_particular(H, s, p):
    rows = [H[i] + [s[i]] for i in range(len(H))]
    red, piv = rref(rows, p)
    n = len(H[0])
    w = [0] * n
    for r, c in enumerate(piv):
        if c == n:
            raise ValueError("inconsistent")
        w[c] = red[r][n]
    return w


def smooth_domain(p, n):
    assert (p - 1) % n == 0
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element")


def ext_from(word, S, xs, k, p):
    if len(S) <= k:
        return True
    base, rest = S[:k], S[k:]
    for j in rest:
        val = 0
        for a in base:
            num, den = 1, 1
            for b in base:
                if b != a:
                    num = num * ((xs[j] - xs[b]) % p) % p
                    den = den * ((xs[a] - xs[b]) % p) % p
            val = (val + word[a] * num * pow(den, p - 2, p)) % p
        if val != word[j] % p:
            return False
    return True


def admissible_mask(subsets, m):
    mask = 0
    for bit, S in enumerate(subsets):
        if len(S) >= m:
            mask |= 1 << bit
    return mask


def build_instance_full(p, n, k):
    xs = smooth_domain(p, n)
    G = [[pow(x, j, p) for x in xs] for j in range(k)]
    H = nullspace(G, p)
    subsets = []
    for size in range(k + 1, n + 1):
        subsets.extend(combinations(range(n), size))
    syndromes = list(product(range(p), repeat=n - k))
    ext_mask = {}
    for s in syndromes:
        w = solve_particular(H, list(s), p)
        mask = 0
        for bit, S in enumerate(subsets):
            if ext_from(w, list(S), xs, k, p):
                mask |= 1 << bit
        ext_mask[s] = mask
    return xs, H, subsets, syndromes, ext_mask


# ---- instance validation: ext_mask vs brute-force codeword agreement ----


def codewords_of(p, k, xs):
    cws = []
    for coeffs in product(range(p), repeat=k):
        cws.append(tuple(sum(c * pow(x, j, p) for j, c in enumerate(coeffs)) % p
                         for x in xs))
    assert len(set(cws)) == p ** k
    return cws


def validate_ext_mask(p, n, k, xs, H, subsets, syndromes, ext_mask):
    cws = codewords_of(p, k, xs)
    for s in syndromes:
        w = solve_particular(H, list(s), p)
        for i, row in enumerate(H):
            assert sum(a * b for a, b in zip(row, w)) % p == s[i]
        for bit, S in enumerate(subsets):
            brute = any(all(w[i] % p == v[i] for i in S) for v in cws)
            assert bool(ext_mask[s] >> bit & 1) == brute, (s, S)


# ---- general syndrome-mask engine (any p, n, k, l; s = 2) ----


def make_base_stacks(syndromes, ext_mask, l):
    out = []
    for stack in product(syndromes, repeat=l):
        joint = -1
        for s in stack:
            joint &= ext_mask[s]
        out.append((stack, joint))
    return out


def make_inter_stacks(syndromes, ext_mask, l):
    cols = list(product(syndromes, repeat=2))
    out = []
    for stack in product(cols, repeat=l):
        rows_a = tuple(w[0] for w in stack)
        rows_b = tuple(w[1] for w in stack)
        joint = -1
        for sa, sb in stack:
            joint &= ext_mask[sa] & ext_mask[sb]
        out.append((rows_a, rows_b, joint))
    return out


def comb_syn(c, rows, p, r):
    return tuple(sum(cj * s[t] for cj, s in zip(c, rows)) % p for t in range(r))


def best_general(Gvals, base_stacks, inter_stacks, ext_mask, adm, p):
    r = len(next(iter(ext_mask)))
    base = {m: 0 for m in adm}
    base_arg = {m: None for m in adm}
    for stack, joint in base_stacks:
        cnt = dict.fromkeys(adm, 0)
        for c in Gvals:
            bad = ext_mask[comb_syn(c, stack, p, r)] & ~joint
            if bad:
                for m, am in adm.items():
                    if bad & am:
                        cnt[m] += 1
        for m in adm:
            if cnt[m] > base[m]:
                base[m], base_arg[m] = cnt[m], stack
    inter = {m: 0 for m in adm}
    inter_arg = {m: None for m in adm}
    for rows_a, rows_b, joint in inter_stacks:
        cnt = dict.fromkeys(adm, 0)
        for c in Gvals:
            ca = comb_syn(c, rows_a, p, r)
            cb = comb_syn(c, rows_b, p, r)
            bad = (ext_mask[ca] & ext_mask[cb]) & ~joint
            if bad:
                for m, am in adm.items():
                    if bad & am:
                        cnt[m] += 1
        for m in adm:
            if cnt[m] > inter[m]:
                inter[m], inter_arg[m] = cnt[m], (rows_a, rows_b)
    return base, base_arg, inter, inter_arg


# ---- fast bitmask path (valid only for n-k = 1 instances; asserted) ----


def assert_fastpath_ok(syndromes, ext_mask, adm):
    zero = tuple(0 for _ in syndromes[0])
    assert len(adm) == 1, "fast path assumes a single admissible radius"
    am = next(iter(adm.values()))
    assert ext_mask[zero] & am
    for s in syndromes:
        if s != zero:
            assert ext_mask[s] == 0, "fast path assumes ext iff syndrome 0"


def fast_pair(Gvals, dot0):
    """base/inter bad-seed maxima for an n-k = 1 instance.

    dot0[c] = tuple over nonzero sigma in F_p^l of (c . sigma == 0).
    A base stack IS a sigma (the l-tuple of word syndromes); seed omega is
    bad iff G(omega) . sigma == 0 (and sigma != 0, else joint).  An
    interleaved stack is a pair of columns (sigma_A, sigma_B); pairs with a
    zero column have the same count as (sigma_A, sigma_A), so nonzero
    column pairs (with repetition) suffice.
    """
    vec = {}
    for i, c in enumerate(Gvals):
        bitsrow = dot0[c]
        for j, hit in enumerate(bitsrow):
            if hit:
                vec[j] = vec.get(j, 0) | (1 << i)
    vecs = set(vec.values())
    vecs.add(0)
    base = max(v.bit_count() for v in vecs)
    inter = max((a & b).bit_count() for a in vecs for b in vecs)
    return base, inter


# ---- independent word-level engine (no syndromes anywhere) ----


def word_engine(Gvals, p, n, k, xs, m_values):
    cws = codewords_of(p, k, xs)
    subsets = []
    for size in range(k + 1, n + 1):
        subsets.extend(combinations(range(n), size))
    adm = {m: admissible_mask(subsets, m) for m in m_values}
    words = list(product(range(p), repeat=n))
    widx = {w: i for i, w in enumerate(words)}
    nw = len(words)
    wm = []
    for w in words:
        mask = 0
        for bit, S in enumerate(subsets):
            if any(all(w[i] == v[i] for i in S) for v in cws):
                mask |= 1 << bit
        wm.append(mask)
    add = [[widx[tuple((a + b) % p for a, b in zip(w1, w2))] for w2 in words]
           for w1 in words]
    smul = [[widx[tuple(s * a % p for a in w)] for w in words]
            for s in range(p)]
    l = len(Gvals[0])

    def comb_idx(c, idxs):
        acc = smul[c[0]][idxs[0]]
        for cj, ui in zip(c[1:], idxs[1:]):
            acc = add[acc][smul[cj][ui]]
        return acc

    base = dict.fromkeys(adm, 0)
    for stack in product(range(nw), repeat=l):
        joint = -1
        for u in stack:
            joint &= wm[u]
        cnt = dict.fromkeys(adm, 0)
        for c in Gvals:
            bad = wm[comb_idx(c, stack)] & ~joint
            if bad:
                for m, am in adm.items():
                    if bad & am:
                        cnt[m] += 1
        for m in adm:
            base[m] = max(base[m], cnt[m])
    inter = dict.fromkeys(adm, 0)
    for stack in product(range(nw), repeat=2 * l):
        rows_a, rows_b = stack[0::2], stack[1::2]
        joint = -1
        for u in stack:
            joint &= wm[u]
        cnt = dict.fromkeys(adm, 0)
        for c in Gvals:
            bad = wm[comb_idx(c, rows_a)] & wm[comb_idx(c, rows_b)] & ~joint
            if bad:
                for m, am in adm.items():
                    if bad & am:
                        cnt[m] += 1
        for m in adm:
            inter[m] = max(inter[m], cnt[m])
    return base, inter


# ---- factor + violation bookkeeping ----


def check_factor(p, base, inter, where, failures):
    """Thm 4.2 transcription at s = 2: inter/|Om| <= (q+1)/q * base/|Om|."""
    if p * inter > (p + 1) * base:
        failures.append(f"FACTOR FAIL at {where}: q*inter={p*inter} > "
                        f"(q+1)*base={(p+1)*base}")


# ---- Parts 1 + 2: RS[F_3, 2, 1] ----


def run_f3(report, failures, violations):
    p, n, k = 3, 2, 1
    xs, H, subsets, syndromes, ext_mask = build_instance_full(p, n, k)
    assert xs == [1, 2] and subsets == [(0, 1)]
    validate_ext_mask(p, n, k, xs, H, subsets, syndromes, ext_mask)
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    assert list(adm) == [2]
    assert_fastpath_ok(syndromes, ext_mask, adm)
    rng = random.Random(891)

    def general_pair(Gvals, bst, ist):
        b, _, i, _ = best_general(Gvals, bst, ist, ext_mask, adm, p)
        return b[2], i[2]

    def handle(Gvals, b, i, where, stats):
        stats["n"] += 1
        stats["max_base"] = max(stats["max_base"], b)
        if i == b:
            stats["eq"] += 1
        if i > b:
            # independent word-level recomputation before reporting
            wb, wi = word_engine(Gvals, p, n, k, xs, [2])
            if wi[2] > wb[2]:
                violations.append((where, Gvals, wb[2], wi[2]))
            else:
                failures.append(f"engine disagreement at {where} G={Gvals}: "
                                f"syndrome=({b},{i}) word=({wb[2]},{wi[2]})")
        check_factor(p, b, i, f"{where} G={Gvals}", failures)

    # -------- Part 1: l = 2, |Omega| in {4, 5}, ALL functions --------
    for l, omega in ((2, 4), (2, 5)):
        all_c = list(product(range(p), repeat=l))
        nz_sig = [s for s in product(range(p), repeat=l) if any(s)]
        dot0 = {c: tuple(sum(a * b for a, b in zip(c, s)) % p == 0
                         for s in nz_sig) for c in all_c}
        bst = make_base_stacks(syndromes, ext_mask, l)
        ist = make_inter_stacks(syndromes, ext_mask, l)
        stats = {"n": 0, "eq": 0, "max_base": 0}
        full_xcheck = omega == 4
        n_xchecked = 0
        for Gvals in product(all_c, repeat=omega):
            b, i = fast_pair(Gvals, dot0)
            if full_xcheck or rng.random() < 0.01:
                gb, gi = general_pair(Gvals, bst, ist)
                assert (gb, gi) == (b, i), \
                    f"fast/general mismatch l={l} |Om|={omega} G={Gvals}"
                n_xchecked += 1
            handle(Gvals, b, i, f"F3 l={l} |Omega|={omega}", stats)
        assert stats["n"] == (p ** l) ** omega
        report.append(
            f"Part1 RS[F_3,2,1] l={l} |Omega|={omega}: {stats['n']} generators "
            f"(ALL functions), inter==base for {stats['eq']}/{stats['n']}, "
            f"max base={stats['max_base']}, engine-xchecked={n_xchecked}")
        # word-level independent cross-check on a sample (+ adversarial pick)
        proj = [(1, 0), (1, 1), (1, 2), (0, 1)]  # the q+1 = 4 directions
        picks = [tuple(proj + ([(1, 0)] * (omega - 4)))]
        picks += [tuple(rng.choice(all_c) for _ in range(omega))
                  for _ in range(60)]
        for Gvals in picks:
            b, i = fast_pair(Gvals, dot0)
            wb, wi = word_engine(Gvals, p, n, k, xs, [2])
            assert (wb[2], wi[2]) == (b, i), \
                f"word-level mismatch l={l} |Om|={omega} G={Gvals}"
        report.append(
            f"  word-level engine agrees on {len(picks)} sampled generators "
            f"(incl. all-4-directions covering generator)")

    # -------- Part 2: l = 3, |Omega| = 4, ALL functions via multisets ----
    l, omega = 3, 4
    all_c = list(product(range(p), repeat=l))
    nz_sig = [s for s in product(range(p), repeat=l) if any(s)]
    dot0 = {c: tuple(sum(a * b for a, b in zip(c, s)) % p == 0
                     for s in nz_sig) for c in all_c}
    bst = make_base_stacks(syndromes, ext_mask, l)
    ist = make_inter_stacks(syndromes, ext_mask, l)
    stats = {"n": 0, "eq": 0, "max_base": 0}
    classes = list(combinations_with_replacement(all_c, omega))
    assert len(classes) == math.comb(len(all_c) + omega - 1, omega) == 27405
    n_xchecked = 0
    for Gvals in classes:
        b, i = fast_pair(Gvals, dot0)
        if rng.random() < 0.01:
            gb, gi = best_general(Gvals, bst, ist, ext_mask, adm, p)[0::2]
            assert (gb[2], gi[2]) == (b, i), f"fast/general mismatch l=3 {Gvals}"
            n_xchecked += 1
        handle(Gvals, b, i, "F3 l=3 |Omega|=4", stats)
    # permutation invariance: a random function == its sorted multiset
    for _ in range(2000):
        Gv = [rng.choice(all_c) for _ in range(omega)]
        assert fast_pair(tuple(Gv), dot0) == \
            fast_pair(tuple(sorted(Gv)), dot0)
    report.append(
        f"Part2 RS[F_3,2,1] l=3 |Omega|=4: {len(classes)} multiset classes = "
        f"all {len(all_c)**omega} functions (perm-invariance asserted x2000), "
        f"inter==base for {stats['eq']}/{stats['n']}, "
        f"max base={stats['max_base']}, engine-xchecked={n_xchecked}")
    # word-level check for l = 3 (expensive: 9^6 interleaved stacks/gen)
    for Gvals in [((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)),
                  tuple(rng.choice(all_c) for _ in range(omega))]:
        b, i = fast_pair(Gvals, dot0)
        wb, wi = word_engine(Gvals, p, n, k, xs, [2])
        assert (wb[2], wi[2]) == (b, i), f"word-level mismatch l=3 G={Gvals}"
    report.append("  word-level engine agrees on 2 generators at l=3")


# ---- Part 3: RS[F_5, 4, 2], l = 2, |Omega| = 6 (sampled generators) ----


def run_f5(report, failures, violations):
    p, n, k, omega = 5, 4, 2, 6
    xs, H, subsets, syndromes, ext_mask = build_instance_full(p, n, k)
    validate_ext_mask(p, n, k, xs, H, subsets, syndromes, ext_mask)
    assert syndromes == list(product(range(p), repeat=2))
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    assert sorted(adm) == [3, 4]
    rng = random.Random(891)
    ns = len(syndromes)  # 25

    ext_list = [ext_mask[s] for s in syndromes]
    jcol_py = [ext_list[i] & ext_list[j]
               for i in range(ns) for j in range(ns)]
    all_c = list(product(range(p), repeat=2))
    comb_flat_py = {}
    for c in all_c:
        flat = []
        for i in range(ns):
            for j in range(ns):
                t = tuple((c[0] * syndromes[i][t0] + c[1] * syndromes[j][t0]) % p
                          for t0 in range(2))
                flat.append(t[0] * p + t[1])
        comb_flat_py[c] = flat

    try:
        import numpy as np
        have_np = True
    except ImportError:
        np, have_np = None, False

    if have_np:
        ext_arr = np.array(ext_list, dtype=np.uint8)
        jcol = np.array(jcol_py, dtype=np.uint8)
        comb_np = {c: np.array(v, dtype=np.int64)
                   for c, v in comb_flat_py.items()}
        jj = jcol[:, None] & jcol[None, :]

        def engine(Gvals):
            ms = np.stack([ext_arr[comb_np[c]] for c in Gvals])  # (om, 625)
            base, inter = {}, {}
            for m, am in adm.items():
                badb = ((ms & ~jcol[None, :] & am) != 0).sum(axis=0)
                base[m] = int(badb.max())
            pair = ms[:, :, None] & ms[:, None, :]  # (om, 625, 625)
            nj = ~jj
            for m, am in adm.items():
                cnt = ((pair & nj[None, :, :] & am) != 0).sum(axis=0)
                inter[m] = int(cnt.max())
            return base, inter
    else:
        def engine(Gvals):
            return pure_engine(Gvals)

    def pure_engine(Gvals):
        ncols = ns * ns
        m_rows = [[ext_list[x] for x in comb_flat_py[c]] for c in Gvals]
        am3, am4 = adm[3], adm[4]
        base = {3: 0, 4: 0}
        for x in range(ncols):
            nj = ~jcol_py[x]
            c3 = c4 = 0
            for row in m_rows:
                t = row[x] & nj
                if t & am3:
                    c3 += 1
                if t & am4:
                    c4 += 1
            base[3] = max(base[3], c3)
            base[4] = max(base[4], c4)
        inter = {3: 0, 4: 0}
        for a in range(ncols):
            ja = jcol_py[a]
            rows_a = [row[a] for row in m_rows]
            for b in range(ncols):
                nj = ~(ja & jcol_py[b])
                c3 = c4 = 0
                for ra, row in zip(rows_a, m_rows):
                    t = ra & row[b] & nj
                    if t & am3:
                        c3 += 1
                    if t & am4:
                        c4 += 1
                if c3 > inter[3]:
                    inter[3] = c3
                if c4 > inter[4]:
                    inter[4] = c4
        return base, inter

    directions = [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (0, 1)]
    gens = [("projective-line(q+1=6 dirs)", tuple(directions))]
    for t in range(40):
        gens.append((f"dir-multiset#{t}",
                     tuple(rng.choice(directions) for _ in range(omega))))
    for t in range(20):
        gens.append((f"scaled-dirs#{t}",
                     tuple(tuple(rng.randrange(1, p) * a % p for a in
                                 rng.choice(directions)) for _ in range(omega))))
    n_random = 400 if have_np else 6
    for t in range(n_random):
        gens.append((f"random#{t}",
                     tuple(rng.choice(all_c) for _ in range(omega))))

    worst = {m: (0.0, None) for m in adm}
    eq_all = 0
    for name, Gvals in gens:
        base, inter = engine(Gvals)
        if all(inter[m] == base[m] for m in adm):
            eq_all += 1
        for m in adm:
            check_factor(p, base[m], inter[m],
                         f"F5 m={m} {name} G={Gvals}", failures)
            if inter[m] > base[m]:
                # independent recomputation before reporting a violation
                pb, pi = pure_engine(Gvals)
                if pi[m] > pb[m]:
                    violations.append((f"F5 m={m} {name}", Gvals,
                                       pb[m], pi[m]))
                else:
                    failures.append(f"engine disagreement on {name} m={m}: "
                                    f"np=({base[m]},{inter[m]}) "
                                    f"pure=({pb[m]},{pi[m]})")
            if base[m]:
                r = inter[m] / base[m]
            else:
                r = 0.0 if inter[m] == 0 else float("inf")
            if r > worst[m][0]:
                worst[m] = (r, (name, Gvals, base[m], inter[m]))
    # numpy-vs-pure cross-check on two generators
    if have_np:
        for name, Gvals in [gens[0], gens[-1]]:
            nb, ni = engine(Gvals)
            pb, pi = pure_engine(Gvals)
            assert (nb, ni) == (pb, pi), f"np/pure mismatch on {name}"
        report.append("Part3 numpy engine == pure engine on 2 generators "
                      "(incl. projective-line)")
    report.append(
        f"Part3 RS[F_5,4,2] l=2 |Omega|=6 (SAMPLED {len(gens)} generators, "
        f"stacks exhaustive 625/390625): inter==base for all m on "
        f"{eq_all}/{len(gens)} generators")
    for m in sorted(adm, reverse=True):
        r, info = worst[m]
        name, Gvals, b, i = info
        report.append(
            f"  m={m} delta={1 - m / n:.2f}: worst inter/base = {r:.3f} "
            f"({name}: base={b}, inter={i}); A(5,2)=1.200")


def main():
    report, failures, violations = [], [], []
    run_f3(report, failures, violations)
    run_f5(report, failures, violations)

    print("=" * 72)
    for line in report:
        print(line)
    print("=" * 72)
    if violations:
        print("VIOLATIONS (inter > base), independently re-verified:")
        for where, Gvals, b, i in violations:
            print(f"  {where}: G={Gvals} base={b} inter={i}")
        print("VERDICT: VIOLATION — the [Jo26] |Omega|<=q dichotomy is real")
    else:
        print("no generator with inter > base found anywhere")
        print("VERDICT: equality-universal-at-toy-scale")
        print("(note: at n-k=1 equality is structurally forced — see module "
              "docstring; the non-forced Part 3 regime is sampled, not "
              "exhaustive, and also showed equality everywhere)")
    if failures:
        print("FAILURES:")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)
    print("factor inequality q*inter <= (q+1)*base held at every instance; "
          "all cross-checks passed")
    sys.exit(0)


if __name__ == "__main__":
    main()
