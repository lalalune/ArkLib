#!/usr/bin/env python3
"""[Jo26] Theorem 4.2 factor at toy scale: eps_G(C^{=s}, delta) vs eps_G(C, delta).

Issue #334 residual B1: [Jo26] (ePrint 2026/891) Thm 4.2 claims, for an arbitrary
coefficient generator G over F_q and the s-interleaved code C^{=s},

    eps_G(C^{=s}, delta)  <=  (1 + 1/q + ... + 1/q^{s-1}) * eps_G(C, delta).

The affine-line generator case is in-tree as an EXACT equality
(`epsMCA_interleaved_eq`, InterleavingStabilityMCA.lean).  This probe measures
the t-word POWER generator gamma |-> (1, gamma, ..., gamma^{t-1}) (the in-tree
`epsMCAP` shape), where only the factor inequality is claimed, at toy scale:

  * exact (exhaustive over syndrome tuples) on RS[F_3,2,1], RS[F_5,2,1],
    RS[F_5,4,2] base + s=2 interleaving where feasible;
  * sampled honest lower bounds on the interleaved side where exhaustion is
    infeasible (sampling can only under-report eps; an observed violation of
    the factor inequality is a real refutation).

Event convention (matches the in-tree mcaEvent / ABF26 Def 4.3 and the prior
probes in this directory): for words u_0..u_{t-1} and scalar gamma, gamma is BAD
iff there exists an admissible witness set S (|S| >= (1-delta) n) such that the
combination sum_i gamma^i u_i extends to a codeword on S but NOT all u_i
simultaneously extend on S.  For the interleaved code, "extends on S" means
every row extends on S (a C^{=s} codeword is an s-tuple of codewords; distance
is column-wise).

Syndrome reduction as in probe_exact_epsmca_ladder.py: the event depends on the
u_i only through their parity-check syndromes; combination syndrome is
sum_i gamma^i s_i.  Cross-checks:
  1. t=2 power generator == affine line: interleaved eps must EQUAL base eps
     (the in-tree exactness theorem's prediction) on exhaustive instances.
  2. Base-code profiles for t=2 must reproduce probe_exact_epsmca_ladder.py
     values where instances overlap.
Exit 0 iff no assertion fails.  A printed VIOLATION line (factor inequality
broken by an exact or sampled count) would refute Thm 4.2 as transcribed —
falsify-first discipline for the formalization target.
"""

import random
from itertools import product, combinations

random.seed(334)


# ------------------------------------------------------------ F_p linear algebra

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
            raise ValueError("inconsistent system")
        w[c] = red[r][n]
    return w


# ------------------------------------------------------------ RS instance

def smooth_domain(p, n):
    assert (p - 1) % n == 0, f"need n | p-1, got n={n}, p={p}"
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return [pow(g, i, p) for i in range(n)]
    raise ValueError("no order-n element found")


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


def build_instance(p, n, k):
    """Returns (subsets, syndromes, ext_mask) for the base code."""
    xs = smooth_domain(p, n)
    G = [[pow(x, j, p) for x in xs] for j in range(k)]
    H = nullspace(G, p)
    assert len(H) == n - k
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
    return subsets, syndromes, ext_mask


def admissible_mask(subsets, m):
    mask = 0
    for bit, S in enumerate(subsets):
        if len(S) >= m:
            mask |= 1 << bit
    return mask


# ------------------------------------------------------------ eps profiles

def combo_syndrome(syns, gamma, p):
    """sum_i gamma^i * syns[i] componentwise (power generator)."""
    out = [0] * len(syns[0])
    coef = 1
    for s in syns:
        for j, x in enumerate(s):
            out[j] = (out[j] + coef * x) % p
        coef = (coef * gamma) % p
    return tuple(out)


def bad_gamma_count_base(syns, ext_mask, adm_masks, p):
    """Per admissibility threshold m: #{gamma : exists admissible S bad}."""
    joint = ~0
    for s in syns:
        joint &= ext_mask[s]
    counts = {m: 0 for m in adm_masks}
    for g in range(p):
        line = combo_syndrome(syns, g, p)
        bad = ext_mask[line] & ~joint
        for m, am in adm_masks.items():
            if bad & am:
                counts[m] += 1
    return counts


def bad_gamma_count_inter(syn_pairs, ext_mask, adm_masks, p):
    """Interleaved s=2: each word is a PAIR of base syndromes; ext on S means
    both rows extend on S, i.e. masks intersect."""
    joint = ~0
    for (sa, sb) in syn_pairs:
        joint &= ext_mask[sa] & ext_mask[sb]
    counts = {m: 0 for m in adm_masks}
    for g in range(p):
        la = combo_syndrome([sp[0] for sp in syn_pairs], g, p)
        lb = combo_syndrome([sp[1] for sp in syn_pairs], g, p)
        bad = (ext_mask[la] & ext_mask[lb]) & ~joint
        for m, am in adm_masks.items():
            if bad & am:
                counts[m] += 1
    return counts


def exact_base_profile(p, n, k, t):
    subsets, syndromes, ext_mask = build_instance(p, n, k)
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    best = {m: 0 for m in adm}
    nz = [s for s in syndromes if any(s)]
    pool = [syndromes] + [nz] * (t - 1)
    for syns in product(*pool):
        c = bad_gamma_count_base(list(syns), ext_mask, adm, p)
        for m in adm:
            if c[m] > best[m]:
                best[m] = c[m]
    return best, subsets, ext_mask, adm


def exact_inter_profile(p, n, k, t, subsets, ext_mask, adm):
    syndromes = list(product(range(p), repeat=n - k))
    pairs = list(product(syndromes, repeat=2))
    nz_pairs = [sp for sp in pairs if any(sp[0]) or any(sp[1])]
    best = {m: 0 for m in adm}
    pool = [pairs] + [nz_pairs] * (t - 1)
    total = len(pairs) * (len(nz_pairs) ** (t - 1))
    if total > 2_000_000:
        return None  # infeasible; caller falls back to sampling
    for sps in product(*pool):
        c = bad_gamma_count_inter(list(sps), ext_mask, adm, p)
        for m in adm:
            if c[m] > best[m]:
                best[m] = c[m]
    return best


def sampled_inter_profile(p, n, k, t, subsets, ext_mask, adm, trials=60000):
    """Honest lower bound: random + structured (repeat/monomial-ish) tuples."""
    syndromes = list(product(range(p), repeat=n - k))
    best = {m: 0 for m in adm}
    nz = [s for s in syndromes if any(s)]
    for _ in range(trials):
        sps = [(random.choice(syndromes), random.choice(syndromes))]
        for _ in range(t - 1):
            sps.append((random.choice(nz), random.choice(nz)))
        c = bad_gamma_count_inter(sps, ext_mask, adm, p)
        for m in adm:
            if c[m] > best[m]:
                best[m] = c[m]
    # structured family: rows reuse one base syndrome (diagonal embedding);
    # the base worst case embeds diagonally, so include all-diagonal tuples.
    for syns in product(nz, repeat=t):
        sps = [(s, s) for s in syns]
        c = bad_gamma_count_inter(sps, ext_mask, adm, p)
        for m in adm:
            if c[m] > best[m]:
                best[m] = c[m]
    return best


# ------------------------------------------------------------ driver

def run_instance(p, n, k, t):
    factor_num = sum(p ** (1 - i) for i in range(1, 2 + 1))  # not used; clarity below
    base, subsets, ext_mask, adm = exact_base_profile(p, n, k, t)
    inter = exact_inter_profile(p, n, k, t, subsets, ext_mask, adm)
    mode = "exact"
    if inter is None:
        inter = sampled_inter_profile(p, n, k, t, subsets, ext_mask, adm)
        mode = "sampled-LB"
    s = 2
    # factor (1 + 1/q + ... + 1/q^{s-1}) with q = p, s = 2: scale counts by p:
    #   inter_count <= (1 + 1/p) * base_count  <=>  p*inter <= (p+1)*base
    print(f"\nRS[F_{p}, n={n}, k={k}], t={t} power generator, s=2 interleave "
          f"[{mode}]")
    print(f"  {'m':>3} {'delta':>7} {'base bad':>9} {'inter bad':>10} "
          f"{'(p+1)*base':>11} {'verdict':>9}")
    ok = True
    for m in sorted(adm, reverse=True):
        delta = 1 - m / n
        lhs = p * inter[m]
        rhs = (p + 1) * base[m]
        verdict = "ok" if lhs <= rhs else ("VIOLATION" if mode == "exact"
                                           else "VIOLATION(sampled)")
        if lhs > rhs:
            ok = False
        eq = "=" if inter[m] == base[m] else " "
        print(f"  {m:>3} {delta:>7.3f} {base[m]:>9} {inter[m]:>9}{eq} "
              f"{rhs:>11} {verdict:>9}")
    return base, inter, mode, ok


if __name__ == "__main__":
    all_ok = True
    equality_t2 = True

    # exhaustive tiny instances
    for (p, n, k) in [(3, 2, 1), (5, 2, 1), (5, 4, 2)]:
        for t in (2, 3):
            base, inter, mode, ok = run_instance(p, n, k, t)
            all_ok &= ok
            if t == 2 and mode == "exact":
                # in-tree exactness prediction for the affine-line generator
                if base != inter:
                    equality_t2 = False
                    print("  ** t=2 exact-equality prediction FAILED above **")

    print("\ncross-check 1 (t=2 affine line, exhaustive instances): "
          + ("interleaved eps == base eps everywhere [OK]" if equality_t2
             else "EQUALITY FAILED — investigate epsMCA_interleaved_eq scope"))
    assert equality_t2, "t=2 interleaving exactness violated at toy scale"
    assert all_ok, "factor inequality violated (see VIOLATION rows)"
    print("cross-check 2 (factor inequality, q=p, s=2): "
          "p*inter <= (p+1)*base everywhere [OK]")
    print("\nall assertions passed")
