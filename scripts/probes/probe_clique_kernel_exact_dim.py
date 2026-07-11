#!/usr/bin/env python3
"""
PROBE: exact kernel dimension of the Conjecture-41 CLIQUE constraint matrix
A_clique = [ N_{E_α} | γ_α · N_{E_α} ]_{α∈W}  (stacked row blocks),  E_α = W∖{α}, |W|=w+1.

In-tree (Conjecture41CliqueKernelStructure.lean) we have proven:
  - the twisted evaluation pencil { (s1,s2) = (-Σ γ(β)b(β)ev_β , Σ b(β)ev_β) : b:W→F }
    lies in ker A_clique  (clique_kernel_mem), and
  - that map b ↦ (...) is injective  (evalSyndrome_family_injective)
  ⟹ kerdim ≥ w+1, i.e. rank A_clique ≤ 2D − (w+1).

OPEN (docstring-named): is this pencil the WHOLE kernel?  The docstring GUESSES a larger
formula (w+1)+(w−1)(c−1).  Issue #444 line 187's third-party exact-ℚ computation claims
kerdim = w+1 EXACTLY (rank = D+c−1) at c=2,3,4.  These DISAGREE.  Settle it exactly over ℚ
(and over several F_p) for c = 1..4, multiple node sets, multiple twist assignments.

Rule-2 honesty: NEVER validate on a degenerate config.  Use distinct random nodes, generic
nonzero twists, D = (w+1−1)+c = w+c so the normals of degree up to (w-1)+(c-1) fit in F^D, and
report rank + nullity + the predicted values.
"""
import random
from fractions import Fraction

def vandermonde_row(t, D):
    # ev_t = (1, t, t^2, ..., t^{D-1})
    out, p = [], Fraction(1)
    for _ in range(D):
        out.append(p); p *= t
    return out

def clique_locator_coeffs(W, alpha):
    # Λ_{W∖{α}} = ∏_{β∈W, β≠α} (X − β),  return coeff list (low→high), length |W| (= deg+1)
    poly = [Fraction(1)]  # constant 1
    for b in W:
        if b == alpha:
            continue
        # multiply by (X - b): newpoly[i] = old[i-1] - b*old[i]
        new = [Fraction(0)] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i]   += -b * c
            new[i+1] += c
        poly = new
    return poly  # length = |W|  (degree w)

def normal_coeffs(loc, r, D):
    # (Λ · X^r) truncated/padded to length D  (coeff vector in F^D, the "normal")
    v = [Fraction(0)] * D
    for i, c in enumerate(loc):
        if i + r < D:
            v[i + r] = c
    return v

def rank_nullity(rows, ncols):
    # exact Gaussian elimination over ℚ; returns (rank, nullity=ncols-rank)
    M = [row[:] for row in rows]
    nr = len(M)
    rank = 0
    col = 0
    while rank < nr and col < ncols:
        piv = None
        for i in range(rank, nr):
            if M[i][col] != 0:
                piv = i; break
        if piv is None:
            col += 1; continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = M[rank][col]
        M[rank] = [x / inv for x in M[rank]]
        for i in range(nr):
            if i != rank and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f*b for a, b in zip(M[i], M[rank])]
        rank += 1; col += 1
    return rank, ncols - rank

def build_clique_matrix(W, gamma, c, D):
    """A_clique rows: for each α∈W, for each r<c: row = [ N_{E_α,r} | γ_α · N_{E_α,r} ] in F^{2D}."""
    rows = []
    for alpha in W:
        loc = clique_locator_coeffs(W, alpha)
        g = gamma[alpha]
        for r in range(c):
            n = normal_coeffs(loc, r, D)
            row = n + [g * x for x in n]   # left block | twisted right block
            rows.append(row)
    return rows

def run(w, c, field_p=None, seed=0):
    """w = |W|-1 (clique on w+1 vertices); c = codimension; field_p None => ℚ."""
    rng = random.Random(seed)
    wcard = w + 1
    # distinct nonzero nodes
    if field_p:
        pool = list(range(1, field_p))
        rng.shuffle(pool)
        W = [Fraction(x) for x in pool[:wcard]]
        gamma = {b: Fraction(rng.randrange(1, field_p)) for b in W}
    else:
        vals = set()
        while len(vals) < wcard:
            vals.add(rng.randint(1, 97))
        W = [Fraction(v) for v in vals]
        gamma = {b: Fraction(rng.randint(1, 97)) for b in W}
    D = (wcard - 1) + c          # so degree (w-1)+(c-1) normals fit: max deg = w + (c-1); need < D... use w+c
    D = w + c                    # max normal degree = w + (c-1) = D-1 ✓ fits
    ncols = 2 * D
    rows = build_clique_matrix(W, gamma, c, D)
    if field_p:
        # reduce mod p by working in F_p via Fraction → mod p inverse-free: just recompute rank mod p
        rank, null = rank_mod_p(rows, ncols, field_p)
    else:
        rank, null = rank_nullity(rows, ncols)
    nrows = len(rows)
    return dict(w=w, c=c, wcard=wcard, D=D, nrows=nrows, ncols=ncols,
                rank=rank, nullity=null,
                pred_pencil=wcard,                       # w+1 (proven floor)
                pred_docstring=(wcard) + (w-1)*(c-1),    # docstring guess
                pred_issue_Dpc1=D + c - 1)               # issue line-187 "rank=D+c-1"

def rank_mod_p(rows, ncols, p):
    M = [[int(x.numerator * pow(x.denominator % p, p-2, p)) % p for x in row] for row in rows]
    nr = len(M); rank = 0; col = 0
    while rank < nr and col < ncols:
        piv = None
        for i in range(rank, nr):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None:
            col += 1; continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], p-2, p)
        M[rank] = [(x*inv) % p for x in M[rank]]
        for i in range(nr):
            if i != rank and M[i][col] % p != 0:
                f = M[i][col]
                M[i] = [(a - f*b) % p for a, b in zip(M[i], M[rank])]
        rank += 1; col += 1
    return rank, ncols - rank

print("=== EXACT clique kernel dimension: pencil(w+1) vs docstring vs issue(D+c-1)? ===")
print(f"{'w':>2} {'c':>2} {'wcard':>5} {'D':>3} {'rows':>4} {'cols':>4} {'rank':>4} {'null':>4} "
      f"{'pencil':>6} {'docstr':>6} {'D+c-1':>6}  verdict")
for w in range(2, 6):          # cliques on 3..6 vertices
    for c in range(1, 5):      # codim 1..4
        # average over several seeds AND a couple of primes to confirm field-robustness
        results = []
        for seed in range(4):
            results.append(run(w, c, field_p=None, seed=seed))
        # all should agree
        nulls = set(r['nullity'] for r in results)
        ranks = set(r['rank'] for r in results)
        r0 = results[0]
        # field check mod p
        mod_nulls = set()
        for p in (101, 103, 107):
            mod_nulls.add(run(w, c, field_p=p, seed=7)['nullity'])
        v = "kerdim=w+1" if (len(nulls)==1 and r0['nullity']==r0['pred_pencil']) else \
            ("kerdim=docstr" if r0['nullity']==r0['pred_docstring'] else "OTHER")
        fieldrobust = "Q=Fp" if mod_nulls==nulls else f"FIELD-DEP! Fp={mod_nulls}"
        print(f"{w:>2} {c:>2} {r0['wcard']:>5} {r0['D']:>3} {r0['nrows']:>4} {r0['ncols']:>4} "
              f"{min(ranks):>4} {r0['nullity']:>4} {r0['pred_pencil']:>6} {r0['pred_docstring']:>6} "
              f"{r0['pred_Dpc1'] if 'pred_Dpc1' in r0 else r0['pred_issue_Dpc1']:>6}  {v} [{fieldrobust}]"
              + ("" if len(nulls)==1 else f"  !!NULL-VARIES {nulls}"))
