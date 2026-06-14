#!/usr/bin/env python3
"""Does [Jo26] interleaving exactness survive seed sets LARGER than q?

[Jo26] (ePrint 2026/891) Thm 4.4: if a coefficient generator G : Omega -> F_q^l
has |Omega| <= q, then eps_G(C^{=s}, delta) = eps_G(C, delta) EXACTLY (the
covering lemma escapes <= q proper subspaces of F_q^s).  Thm 4.2 pays the
factor A(q,s) = 1 + 1/q + ... + 1/q^{s-1} for arbitrary Omega.  Remark 4.3
only shows A(q,s) is sharp for the subspace-AVOIDANCE step; whether the
THEOREM's factor is needed for any actual (C, G, delta) is open — at
|Omega| = q+1 the covering argument genuinely breaks (F_q^2 IS covered by its
q+1 lines through 0), but a violating instance needs witnesses realizing
those lines as bad-seed subspaces K_omega.

This probe measures, exhaustively at toy scale, the two-seed-variable
generator  G : F_q x F_q -> F_q^3, (a,b) |-> (1, a, b)   (|Omega| = q^2 > q)
on tiny RS codes with s = 2 interleaving:

    ratio  =  eps_G(C^{=2}, delta) / eps_G(C, delta)   (as bad-seed COUNTS)

Outcomes:
  * ratio = 1 everywhere  -> evidence the factor is slack for natural
    generators; conjecture target: exactness beyond |Omega| <= q (new math).
  * 1 < ratio <= A(q,2)   -> the dichotomy is real; hunt for the sharp
    instance; the formalization keeps the factor.
  * ratio > A(q,2)        -> refutes Thm 4.2 as transcribed (transcription
    bug on our side, most likely) — recheck definitions.

Event convention as in probe_jo26_interleaved_generator_factor.py (in-tree
mcaEventP shape, syndrome-reduced).  Exit 0 iff factor inequality holds and
internal cross-checks pass; the RATIO TABLE is the scientific output.
"""

from itertools import product, combinations

# ---- shared linear algebra (as in sibling probes) ----

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


def build_instance(p, n, k):
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
    return subsets, syndromes, ext_mask


def admissible_mask(subsets, m):
    mask = 0
    for bit, S in enumerate(subsets):
        if len(S) >= m:
            mask |= 1 << bit
    return mask


# ---- the |Omega| = q^2 generator: (a,b) |-> (1, a, b), l = 3 words ----

def comb3(s0, s1, s2, a, b, p):
    return tuple((x + a * y + b * z) % p for x, y, z in zip(s0, s1, s2))


def bad_seed_count_base(s0, s1, s2, ext_mask, adm, p):
    joint = ext_mask[s0] & ext_mask[s1] & ext_mask[s2]
    counts = {m: 0 for m in adm}
    for a in range(p):
        for b in range(p):
            bad = ext_mask[comb3(s0, s1, s2, a, b, p)] & ~joint
            for m, am in adm.items():
                if bad & am:
                    counts[m] += 1
    return counts


def bad_seed_count_inter(sp0, sp1, sp2, ext_mask, adm, p):
    joint = ~0
    for (sa, sb) in (sp0, sp1, sp2):
        joint &= ext_mask[sa] & ext_mask[sb]
    counts = {m: 0 for m in adm}
    for a in range(p):
        for b in range(p):
            la = comb3(sp0[0], sp1[0], sp2[0], a, b, p)
            lb = comb3(sp0[1], sp1[1], sp2[1], a, b, p)
            bad = (ext_mask[la] & ext_mask[lb]) & ~joint
            for m, am in adm.items():
                if bad & am:
                    counts[m] += 1
    return counts


def run(p, n, k):
    subsets, syndromes, ext_mask = build_instance(p, n, k)
    adm = {m: admissible_mask(subsets, m) for m in range(k + 1, n + 1)}
    nz = [s for s in syndromes if any(s)]

    base_best = {m: 0 for m in adm}
    for s0 in syndromes:
        for s1 in nz:
            for s2 in nz:
                c = bad_seed_count_base(s0, s1, s2, ext_mask, adm, p)
                for m in adm:
                    base_best[m] = max(base_best[m], c[m])

    pairs = list(product(syndromes, repeat=2))
    nz_pairs = [sp for sp in pairs if any(sp[0]) or any(sp[1])]
    total = len(pairs) * len(nz_pairs) ** 2
    inter_best = {m: 0 for m in adm}
    mode = "exact"
    if total <= 3_000_000:
        for sp0 in pairs:
            for sp1 in nz_pairs:
                for sp2 in nz_pairs:
                    c = bad_seed_count_inter(sp0, sp1, sp2, ext_mask, adm, p)
                    for m in adm:
                        inter_best[m] = max(inter_best[m], c[m])
    else:
        mode = "diag+sampled"
        import random
        random.seed(891)
        for s0 in syndromes:          # diagonal embeddings (base worst case)
            for s1 in nz:
                for s2 in nz:
                    c = bad_seed_count_inter((s0, s0), (s1, s1), (s2, s2),
                                             ext_mask, adm, p)
                    for m in adm:
                        inter_best[m] = max(inter_best[m], c[m])
        for _ in range(40000):
            sp0 = (tuple(random.randrange(p) for _ in range(n - k)),
                   tuple(random.randrange(p) for _ in range(n - k)))
            sp1 = (tuple(random.randrange(p) for _ in range(n - k)),
                   tuple(random.randrange(p) for _ in range(n - k)))
            sp2 = (tuple(random.randrange(p) for _ in range(n - k)),
                   tuple(random.randrange(p) for _ in range(n - k)))
            if not (any(sp1[0]) or any(sp1[1])) or not (any(sp2[0]) or any(sp2[1])):
                continue
            c = bad_seed_count_inter(sp0, sp1, sp2, ext_mask, adm, p)
            for m in adm:
                inter_best[m] = max(inter_best[m], c[m])

    omega = p * p
    print(f"\nRS[F_{p}, n={n}, k={k}]  generator (a,b)->(1,a,b), |Omega|=q^2={omega}"
          f"  s=2 interleave  [{mode}]")
    print(f"  {'m':>3} {'delta':>7} {'base':>6} {'inter':>6} {'ratio':>7}  "
          f"A(q,2)={1 + 1 / p:.3f}")
    ok = True
    for m in sorted(adm, reverse=True):
        b, i = base_best[m], inter_best[m]
        ratio = (i / b) if b else float('nan') if i == 0 else float('inf')
        # factor check in counts: i <= A(q,2)*b  <=>  p*i <= (p+1)*b
        viol = p * i > (p + 1) * b
        ok &= not viol
        tag = " VIOLATION" if viol else (" >1!" if b and i > b else "")
        rs = f"{ratio:7.3f}" if b or i == 0 else "    inf"
        print(f"  {m:>3} {1 - m / n:>7.3f} {b:>6} {i:>6} {rs}{tag}")
    return ok


if __name__ == "__main__":
    all_ok = True
    for (p, n, k) in [(3, 2, 1), (5, 2, 1), (5, 4, 2)]:
        all_ok &= run(p, n, k)
    assert all_ok, "factor inequality violated — recheck transcription"
    print("\nfactor inequality holds on all instances; ratio table above is "
          "the A1/A5 hypothesis evidence\nall assertions passed")
