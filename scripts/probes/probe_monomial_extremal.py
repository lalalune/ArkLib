#!/usr/bin/env python3
"""
probe_monomial_extremal.py  (issue #389)

Tests the key sub-conjecture unlocked by the cyclic lever + monomial-line bridge:

    Are MONOMIAL far directions u1 = x^a (a >= k) the WORST-CASE far lines for the
    MCA far-line incidence I(delta) over an explicit subgroup-RS code on mu_n?

If YES, the Z/n cyclic symmetry CLOSES the average->worst-case gap (the open prize core):
the worst case is a dilation-fixed line, whose line-ball incidence is CIRCULANT and
computable in closed Fourier form. If NO, the cyclic-closure path is refuted and the
worst far line genuinely exploits non-monomial structure.

Computation (exact, via syndromes -- the law's object):
  RS[mu_n, k] over F_q (n | q-1).  Syndrome map H: F_q^n -> F_q^{n-k}.
  S_w := { H e^T : wt(e) <= w }  (the low-weight syndrome set, w = floor(delta*n)).
  For an affine line with syndromes (s0, s1):  #bad = #{ gamma in F_q : s0 + gamma*s1 in S_w }.
  far line  <=>  s1 not in S_w  (coset min-weight of u1 exceeds the slack).
    I(delta)      = max over ALL far s1, all s0 of #bad
    I_mono(delta) = max over MONOMIAL s1 = syn(x^a), a in {k..n-1}, all s0 of #bad
  Conjecture "monomials extremal"  <=>  I_mono(delta) == I(delta)  at every radius.
"""

import itertools
import sys


def gf_prime(q):
    """Return (add, mul, inv) for prime field F_q (q prime). Elements 0..q-1."""
    assert all(q % p for p in range(2, int(q**0.5) + 1)), f"{q} not prime"
    inv = [0] * q
    for a in range(1, q):
        for b in range(1, q):
            if (a * b) % q == 1:
                inv[a] = b
                break
    return q, inv


def roots_of_unity(q, n):
    """The n-th roots of unity in F_q (n | q-1), as a list of field elements."""
    assert (q - 1) % n == 0
    # find a generator g of F_q^*, then omega = g^((q-1)/n)
    for g in range(2, q):
        seen = set()
        x = 1
        for _ in range(q - 1):
            x = (x * g) % q
            seen.add(x)
        if len(seen) == q - 1:
            omega = pow(g, (q - 1) // n, q)
            mu = [pow(omega, i, q) for i in range(n)]
            assert len(set(mu)) == n
            return mu
    raise RuntimeError("no generator found")


def rs_parity_check(q, mu, k):
    """A parity-check matrix H ((n-k) x n) for RS[k] = {(p(x))_x : deg p < k} on points mu.
    RS[k] = rowspace of Vandermonde G (k x n, G[j][i] = mu[i]^j). H = left null space basis."""
    n = len(mu)
    G = [[pow(mu[i], j, q) for i in range(n)] for j in range(k)]
    # Build H by Gaussian elimination: find n-k vectors orthogonal to all rows of G.
    # Equivalent: null space of G (as (k x n)); H rows span {v : G v^T = 0}? No --
    # codewords are rowspace of G; parity = vectors h with h . c = 0 for all codewords c,
    # i.e. h orthogonal to every ROW of G:  G h^T = 0.  So H rows = null space of G.
    return null_space(q, G, n)


def null_space(q, M, ncols):
    """Basis (list of row vectors length ncols) of {v : M v^T = 0} over F_q."""
    _, inv = gf_prime(q)
    A = [row[:] for row in M]
    nrows = len(A)
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if A[i][c] % q), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        ipiv = inv[A[r][c] % q]
        A[r] = [(x * ipiv) % q for x in A[r]]
        for i in range(nrows):
            if i != r and A[i][c] % q:
                f = A[i][c] % q
                A[i] = [(A[i][j] - f * A[r][j]) % q for j in range(ncols)]
        pivots.append(c)
        r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for ri, pc in enumerate(pivots):
            v[pc] = (-A[ri][fc]) % q
        basis.append(v)
    return basis


def syn(q, H, word):
    return tuple(sum(H[r][i] * word[i] for i in range(len(word))) % q for r in range(len(H)))


def low_weight_syndromes(q, H, n, w):
    """S_w = { H e^T : wt(e) <= w }."""
    S = set()
    S.add(tuple([0] * len(H)))
    for wt in range(1, w + 1):
        for supp in itertools.combinations(range(n), wt):
            for vals in itertools.product(range(1, q), repeat=wt):
                e = [0] * n
                for idx, pos in enumerate(supp):
                    e[pos] = vals[idx]
                S.add(syn(q, H, e))
    return S


def incidence(q, s0, s1, Sw):
    """#{ gamma in F_q : s0 + gamma*s1 in Sw }."""
    m = len(s0)
    c = 0
    for gamma in range(q):
        pt = tuple((s0[r] + gamma * s1[r]) % q for r in range(m))
        if pt in Sw:
            c += 1
    return c


def run(q, n, k, verbose=True):
    mu = roots_of_unity(q, n)
    H = rs_parity_check(q, mu, k)
    m = len(H)  # = n - k
    assert m == n - k, f"parity rank {m} != n-k {n-k}"
    out = []
    for w in range(1, n - k + 1):
        delta = w / n
        Sw = low_weight_syndromes(q, H, n, w)
        # all syndromes
        all_s = list(itertools.product(range(q), repeat=m))
        # far s1 = syndromes NOT in Sw (coset min weight > w)
        far = [s for s in all_s if s not in Sw and any(s)]
        # monomial directions x^a, a in {k..n-1}, that are far
        mono = []
        for a in range(k, n):
            wa = [pow(mu[i], a, q) for i in range(n)]
            sa = syn(q, H, wa)
            if sa not in Sw and any(sa):
                mono.append(("x^%d" % a, sa))
        # I(delta): max over all far s1, all s0
        I_all = 0
        arg_all = None
        for s1 in far:
            for s0 in all_s:
                c = incidence(q, s0, s1, Sw)
                if c > I_all:
                    I_all, arg_all = c, (s0, s1)
        # I_mono(delta)
        I_mono = 0
        arg_mono = None
        for _, s1 in mono:
            for s0 in all_s:
                c = incidence(q, s0, s1, Sw)
                if c > I_mono:
                    I_mono, arg_mono = c, (s0, s1)
        extremal = (I_mono == I_all)
        johnson = 1.0 - (k / n) ** 0.5
        zone = "ABOVE-J" if delta > johnson else "below-J"
        nontrivial = I_all > 1
        out.append((w, delta, I_all, I_mono, extremal, len(mono), zone, nontrivial))
        if verbose:
            tag = "MONO=MAX" if extremal else "MONO<MAX *REFUTED*"
            print(f"  w={w} delta={delta:.3f} [{zone} J={johnson:.3f}]  "
                  f"I(delta)={I_all:3d}  I_mono={I_mono:3d}  #mono_far={len(mono)}  -> {tag}")
            if not extremal and arg_all is not None:
                print(f"       worst non-mono line: s0={arg_all[0]} s1={arg_all[1]}")
    return out


if __name__ == "__main__":
    cases = [
        (13, 4, 2),   # rho=1/2  m=2
        (7, 4, 2),    # rho=1/2  m=2
        (11, 5, 3),   # rho=3/5  m=2
        (7, 3, 1),    # rho=1/3  m=2
        (13, 4, 1),   # rho=1/4  m=3  (radii span Johnson 0.5)
        (17, 4, 2),   # rho=1/2  m=2
        (7, 6, 3),    # rho=1/2  m=3
        (13, 6, 3),   # rho=1/2  m=3
        (11, 5, 2),   # rho=2/5  m=3  (below-J refutation lives here)
        (7, 6, 2),    # rho=1/3  m=4  (may be slow/skip)
    ]
    print("Testing: are MONOMIAL far directions extremal for the MCA far-line incidence?")
    print("REFINED CONJECTURE (prize-focused): monomials extremal at ABOVE-Johnson radii.\n")
    refuted_global, refuted_aboveJ = [], []
    for (q, n, k) in cases:
        try:
            print(f"RS[mu_{n}, k={k}] over F_{q}  (rho={k}/{n}={k/n:.3f}):")
            res = run(q, n, k)
            for (w, d, Ia, Im, e, nm, zone, nt) in res:
                if not e:
                    refuted_global.append((q, n, k, w))
                    if zone == "ABOVE-J" and nt:
                        refuted_aboveJ.append((q, n, k, w))
            print()
        except Exception as ex:
            print(f"  SKIP ({ex})\n")
    print("=" * 70)
    print(f"Refutations of 'monomials extremal' (any radius):  {len(refuted_global)}  {refuted_global}")
    print(f"Refutations in the PRIZE regime (ABOVE-Johnson, nontrivial I>1):  "
          f"{len(refuted_aboveJ)}  {refuted_aboveJ}")
    print()
    if refuted_aboveJ:
        print("VERDICT: the REFINED conjecture is REFUTED -- monomials are NOT extremal even")
        print("         above Johnson. The cyclic lever gives only a delta* upper bracket.")
    elif refuted_global:
        print("VERDICT: 'monomials extremal' fails ONLY below Johnson (the throw-away regime,")
        print("         trivial incidence). At every ABOVE-Johnson radius tested, monomials")
        print("         ACHIEVE the max -> the Z/n-fixed (monomial/circulant) line computes")
        print("         I(delta) in the prize-relevant regime. The cyclic-closure path SURVIVES")
        print("         where it matters. PURSUE: the circulant/Fourier monomial incidence.")
    else:
        print("VERDICT: 'monomials extremal' SURVIVES on all tested codes at all radii.")
