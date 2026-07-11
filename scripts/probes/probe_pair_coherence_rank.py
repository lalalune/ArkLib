#!/usr/bin/env python3
"""Probe (issue #389, route 2): the rank of paired coherence conditions.

PRE-REGISTERED HYPOTHESES. Generator space c in F^M, Qc = sum c_j X^j.
Per (k+m+1)-core T: m coherence functionals phi_{T,j}(c) = coeff_{k+1+j}(I_T(Qc)),
value functional v_T(c) = -coeff_k(I_T(Qc)). All linear in c. For a pair (T,T'),
T != T', the pair-event conditions are the 2m+1 functionals
  (phi_{T,1..m}, phi_{T',1..m}, v_T - v_{T'}).

H1 (disjoint rank): for T cap T' = empty and M >= 2(k+m+1), rank = 2m+1 ALWAYS.
H2 (small-overlap rank): for |T cap T'| <= k, rank = 2m+1 ALWAYS
    (mechanism: the conditional map values(T'\\T) -> coeffs has a monic-leading
    triangular dual polynomial of degree <= m, so <= m zeros < |T'\\T| = k+m+1-i).
H3 (deep strata): for k+1 <= i <= k+m, rank can drop below 2m+1 (degeneracy
    exists) but never below m+1 (the T-side m conditions + value-difference...
    measure the actual minimum).
H4 (the per-core family): the m+1 functionals (phi_{T,1..m}, v_T) have rank m+1
    for every single core (needed for the diagonal stratum).

Instances: p in {13, 17}, smooth-ish domains (subgroup where available and a
generic domain), k in {2,3}, m in {1,2}, n in {8, 10}, M = 2(k+m+1).
Exhaustive over all core pairs.
"""

import itertools, sys

def inv(a, p): return pow(a % p, p - 2, p)

def lagrange_coeffs(points, p):
    """coeff matrix: rows = coefficient degrees 0..len(points)-1, cols = points;
    entry[d][x-index] = coeff_d(L_x)."""
    t = len(points)
    V = [1]
    for x in points:
        newV = [0]*(len(V)+1)
        for i, c in enumerate(V):
            newV[i+1] = (newV[i+1] + c) % p
            newV[i] = (newV[i] - x*c) % p
        V = newV
    cols = []
    for x in points:
        # q = V/(X-x) by synthetic division; L_x = q / q(x)
        t_deg = len(V) - 1
        q = [0]*t_deg
        carry = 0
        for d in range(t_deg, 0, -1):
            carry = (V[d] + x*carry) % p
            q[d-1] = carry
        qx = 0
        for d in range(t_deg-1, -1, -1):
            qx = (qx*x + q[d]) % p
        iq = inv(qx, p)
        cols.append([(c*iq) % p for c in q])
    # transpose: rows by degree
    return [[cols[j][d] for j in range(t)] for d in range(t)]

def functional_matrix(domain, T_idx, k, m, M, p, include_value=True):
    """rows: for j=1..m the functional c |-> coeff_{k+j}(I_T(Qc)); plus
    (if include_value) c |-> coeff_k. Row vector over c in F^M:
    coeff_d(I_T(Qc)) = sum_x L-coeff[d][x] * Qc(x) = sum_x Lc[d][x] * sum_e c_e x^e."""
    pts = [domain[i] for i in T_idx]
    Lc = lagrange_coeffs(pts, p)
    rows = []
    degs = ([k + j for j in range(1, m+1)] + ([k] if include_value else []))
    for d in degs:
        row = [0]*M
        for xi, x in enumerate(pts):
            w = Lc[d][xi]
            pw = 1
            for e in range(M):
                row[e] = (row[e] + w*pw) % p
                pw = (pw*x) % p
        rows.append(row)
    return rows  # order: coherence rows then value row

def rank(rows, p):
    rows = [r[:] for r in rows]
    nr = len(rows); nc = len(rows[0]) if rows else 0
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        ivv = inv(rows[r][c], p)
        rows[r] = [(a*ivv) % p for a in rows[r]]
        for i in range(nr):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f*b) % p for a, b in zip(rows[i], rows[r])]
        r += 1
    return r

def run(p, domain, k, m, label):
    n = len(domain)
    t = k + m + 1
    M = 2*t
    full = 2*m + 1
    # H4 first: per-core rank m+1
    h4_min = m + 1
    for T in itertools.combinations(range(n), t):
        rows = functional_matrix(domain, T, k, m, M, p, include_value=True)
        h4_min = min(h4_min, rank(rows, p))
    # pair scans
    stats = {}   # overlap -> (min_rank, max_rank, n_deficient, n_pairs)
    cores = list(itertools.combinations(range(n), t))
    for a in range(len(cores)):
        Ta = cores[a]
        rows_a = functional_matrix(domain, Ta, k, m, M, p, include_value=True)
        coh_a, val_a = rows_a[:m], rows_a[m]
        for b in range(a+1, len(cores)):
            Tb = cores[b]
            i = len(set(Ta) & set(Tb))
            rows_b = functional_matrix(domain, Tb, k, m, M, p, include_value=True)
            coh_b, val_b = rows_b[:m], rows_b[m]
            vdiff = [(x - y) % p for x, y in zip(val_a, val_b)]
            R = rank(coh_a + coh_b + [vdiff], p)
            mn, mx, dfc, cnt = stats.get(i, (99, -1, 0, 0))
            stats[i] = (min(mn, R), max(mx, R), dfc + (1 if R < full else 0), cnt + 1)
    print(f"[{label}] p={p} n={n} k={k} m={m} t={t} M={M} target-rank={full} "
          f"| per-core min rank (H4, want {m+1}): {h4_min}")
    for i in sorted(stats):
        mn, mx, dfc, cnt = stats[i]
        zone = "H1" if i == 0 else ("H2" if i <= k else "H3-deep")
        print(f"   overlap {i} ({zone}): rank in [{mn},{mx}], "
              f"deficient {dfc}/{cnt}")

# subgroup domain mu_6 in F_13 (g=4: ord 6); generic 1..8 in F_13; mu_8 in F_17
mu6_13 = []
x = 1
for _ in range(6):
    mu6_13.append(x); x = (x*4) % 13
run(13, mu6_13 + [7, 11][:2], 2, 1, "F13 mu6+2 n=8")     # mixed domain n=8
run(13, list(range(1, 9)), 2, 1, "F13 generic n=8")
mu8_17 = []
x = 1
for _ in range(8):
    mu8_17.append(x); x = (x*2) % 17
run(17, mu8_17, 2, 1, "F17 mu8 n=8")
run(17, mu8_17, 3, 1, "F17 mu8 n=8 k3")
run(17, mu8_17 + [3, 5], 2, 2, "F17 mu8+2 n=10 m2")
run(13, list(range(1, 11)), 2, 2, "F13 generic n=10 m2")

# ---- RESULTS (2026-06-12, pre-registered run) ----
# H1 CONFIRMED: overlap 0 -> rank 2m+1, deficient 0 (all instances).
# H2 CONFIRMED: 1 <= overlap <= k -> rank 2m+1, deficient 0 (all instances).
# H3 SHARPENED TO AN EXACT LAW: overlap i in [k+1, k+m] -> rank = 2m+1-(i-k),
#    with NO variance (every pair at the stratum has exactly that rank).
#    Unified law: rank(T,T') = 2m+1 - max(0, |T cap T'| - k).
# H4 CONFIRMED: per-core (m coherence + value) rank = m+1 always.
# Payoff probe (p=17, n=16, k=2, m=1, M=8, 3000 samples):
#    E[N1] 107.2 vs exact P/q 107.1; E[N2] 1062.4 vs strata-exact 1065.4;
#    distinct values per c: median = max = 17 = q (SATURATION), mean 16.92.
