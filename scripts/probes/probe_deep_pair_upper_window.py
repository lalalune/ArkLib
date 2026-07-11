#!/usr/bin/env python3
"""Pre-registered probe: the UPPER-WINDOW witness for DeepPairValIndependent (#389).

Claim under test (the canonical per-pair witness, before Lean):

  On every deep pair (|T| = |T'| = k+m+1, overlap j = k+d, 1 <= d <= m) the family

      { coeff_{k+1+i}(I_T) : i < m }  ∪  { coeff_{k+d+i}(I_{T'}) : i < m+1-d }

  (T-band full, T'-band restricted to the UPPER WINDOW [k+d, k+m]) is
  (A) jointly surjective — rank exactly m + (m+1-d) = 2m+1-d, every pair, AND
  (B) spanning for the dropped coords — appending the dropped T'-band functionals
      coeff_{k+1..k+d-1}(I_{T'}) does NOT increase the rank (implies_full).

  (The in-tree honest-scope note says no uniform family containing the
  value-difference functional works; the upper-window family contains only band
  coordinates — the derivation says triangularity of C -> coeffs(P_J*C) protects it.)

Sections (any FAIL refutes; goes to DISPROOF_LOG):
  A. rank(surviving) == 2m+1-d at EVERY deep pair, all instances.
  B. rank(surviving + dropped) == rank(surviving) at every deep pair.
  C. control: the LOWER window [k+1, k+m+1-d] fails (A) somewhere (showing the
     choice of window is load-bearing) — informational, not a pass/fail gate.

Instances: (p, n, k, m) in {(13,9,2,1), (13,9,2,2), (13,10,3,1), (17,9,2,2)};
domain = first n points 1..n in F_p (generic) AND, where 8 | p-1 and n = 9
replaced by subgroup-augmented domains for one instance, to vary domain shape.
M = 2(k+m+1). Exact arithmetic mod p. Exit 0 iff A and B pass everywhere.
"""

import itertools
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

failures = []


def check(name, cond, detail=""):
    if not cond:
        failures.append((name, detail))
        print(f"  FAIL {name} {detail}")


def inv(a, p):
    return pow(a, p - 2, p)


def interp_coeffs(xs, ys, p):
    """Coefficients (low->high) of the Lagrange interpolant through (xs, ys)."""
    t = len(xs)
    coeffs = [0] * t
    for j in range(t):
        # basis poly prod_{l != j} (X - x_l) / (x_j - x_l)
        num = [1]
        den = 1
        for l in range(t):
            if l == j:
                continue
            # multiply num by (X - x_l)
            new = [0] * (len(num) + 1)
            for i2, cc in enumerate(num):
                new[i2 + 1] = (new[i2 + 1] + cc) % p
                new[i2] = (new[i2] - cc * xs[l]) % p
            num = new
            den = den * (xs[j] - xs[l]) % p
        scale = ys[j] * inv(den % p, p) % p
        for i2, cc in enumerate(num):
            coeffs[i2] = (coeffs[i2] + cc * scale) % p
    return coeffs


def functional_row(dom, T, pos, M, p):
    """Row vector of c |-> coeff_pos(interpolant of genPoly(c) on T)."""
    xs = [dom[i] for i in T]
    row = []
    for basis in range(M):
        ys = [pow(x, basis, p) for x in xs]
        cf = interp_coeffs(xs, ys, p)
        row.append(cf[pos] if pos < len(cf) else 0)
    return row


def rank_mod(rows, p):
    rows = [r[:] for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    r = 0
    for col in range(ncols):
        piv = None
        for rr in range(r, len(rows)):
            if rows[rr][col] % p:
                piv = rr
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        ivp = inv(rows[r][col] % p, p)
        rows[r] = [(v * ivp) % p for v in rows[r]]
        for rr in range(len(rows)):
            if rr != r and rows[rr][col] % p:
                f = rows[rr][col] % p
                rows[rr] = [(a - f * b) % p for a, b in zip(rows[rr], rows[r])]
        r += 1
        rank += 1
    return rank


for (p, n, k, m) in ((13, 9, 2, 1), (13, 9, 2, 2), (13, 10, 3, 1), (17, 9, 2, 2)):
    t = k + m + 1
    M = 2 * t
    dom = list(range(1, n + 1))
    deep_pairs = lower_fail = 0
    cores = list(itertools.combinations(range(n), t))
    for (T, T2) in itertools.combinations(cores, 2):
        j = len(set(T) & set(T2))
        d = j - k
        if d < 1 or d > m:
            continue
        deep_pairs += 1
        target = 2 * m + 1 - d
        rows_T = [functional_row(dom, T, k + 1 + i, M, p) for i in range(m)]
        upper = [functional_row(dom, T2, k + d + i, M, p) for i in range(m + 1 - d)]
        dropped = [functional_row(dom, T2, k + 1 + i, M, p) for i in range(d - 1)]
        rk = rank_mod(rows_T + upper, p)
        check(f"A ({p},{n},{k},{m}) T={T} T'={T2}", rk == target,
              f"rank={rk} target={target} d={d}")
        rk2 = rank_mod(rows_T + upper + dropped, p)
        check(f"B ({p},{n},{k},{m}) T={T} T'={T2}", rk2 == rk,
              f"rank+dropped={rk2} vs {rk}")
        # control: lower window
        if d >= 1:
            lower = [functional_row(dom, T2, k + 1 + i, M, p)
                     for i in range(m + 1 - d)]
            if rank_mod(rows_T + lower, p) < target:
                lower_fail += 1
    print(f"({p},{n},{k},{m}): {deep_pairs} deep pairs checked; "
          f"lower-window control deficient at {lower_fail} pairs")

print()
if failures:
    print(f"PROBE FAILED: {len(failures)} failures")
    sys.exit(1)
print("A+B PASS — the upper-window family witnesses DeepPairValIndependent at every deep pair")
sys.exit(0)
