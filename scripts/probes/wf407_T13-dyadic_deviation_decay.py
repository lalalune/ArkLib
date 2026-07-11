"""
wf407 / T13-dyadic : per-level deviation delta_i of the 2-adic Gauss-period cocycle.

Thread 407-T13: "Dyadic-deviation-decay delta_i = O(1/i) for the 2-adic cocycle".
Census row: constant excess in the cocycle -> power n^{c(delta)} (PROVEN fatal);
what is needed is the O(1/i) decay rate. TOWER-2 decoupling and M(2n)^2 <= 2 M(n)^2
are already REFUTED (ratios to 3.86) -- we do NOT redo those.

EXACT substrate (Sweep_A12_PhaseAlignmentTower.lean, gaussPeriod_tower_parallelogram):
  Let mu_{2n} = mu_n  union  z*mu_n   (z a primitive 2n-th root, mu_n = <z^2>).
  A := eta_b(mu_n),  B := eta_{b z}(mu_n).  Then
      eta_b(mu_{2n}) = A + B            (untwisted child sum)
      eta^chi_b      = A - B            (twisted child sum)
      ||A+B||^2 + ||A-B||^2 = 2(||A||^2 + ||B||^2)   (EXACT parallelogram cocycle)
  => ||A+B||^2 = ||A||^2 + ||B||^2 + 2 Re(A conj B).

The "pure doubling" / Gaussian law is  ||child||^2 = 2 * (parent worst)^2  (i.e. the
cross term vanishes and both children equal the worst).  The DEVIATION is the cross-term
excess that the cocycle adds on top of the pure doubling at the worst frequency.

We define delta_i MULTIPLICATIVELY at level i (subgroup mu_{2^i}) several rigorous ways,
exactly, and ask: does delta_i decay like O(1/i), slower, or not at all?

  M_i        := max_{b != 0} ||eta_b(mu_{2^i})||                 (worst period, level i)
  Gaussian_i := sqrt(2^i * ln m_i),  m_i = (p-1)/2^i              (the proven sqrt(n log) law)

  (D1)  rho_i := M_i^2 / (2 * M_{i-1}^2)         -- the doubling ratio (REFUTED >1, but
                                                    we track its EXCESS decay, not the bound)
        excess_i := rho_i - 1                     -- this is the per-level cocycle excess
  (D2)  At the worst b* of level i, the cross-term coherence at the level-(i-1) split:
        cos_i := Re(A conj B) / (||A|| ||B||)     -- the alignment (389-T03 cos=1 object)
        the deviation of the WORST-period growth from Gaussian: see (D3)
  (D3)  c_i := M_i^2 / (2^i * ln m_i)  - 1        -- deviation of M_i from the sqrt(n log) law
  (D4)  the additive per-level deviation  d_i := log2(M_i^2) - log2(2 * M_{i-1}^2)
        = log2(rho_i)  (cumulative sum telescopes to the total log-excess; if d_i ~ 1/i
        the cumulative is O(log i) = harmless, if d_i -> const the cumulative is O(i) = fatal)

A constant excess (d_i -> c > 0) compounds to M_{a}^2 >= 2^a * 2^{c*a} = n * n^c => power
n^{c} overshoot = FATAL (this is the "constant excess -> power n^{c(delta)}" the census records).
O(1/i) decay (d_i ~ C/i) gives cumulative Sum d_i ~ C log a = C log log n => only a
poly-LOG overshoot factor => the floor M = O(sqrt(n log n)) SURVIVES.

We sweep primes with odd_part((p-1)/2^i) > 1 (exclude the Fermat #400 trap) so the deep
tower is non-degenerate, and take the LARGEST-scale enumerable subgroups.
"""
import cmath, math, sys

def factorint(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

class _sympy_shim:
    @staticmethod
    def primitive_root(p):
        return primitive_root(p)
    @staticmethod
    def factorint(n):
        return factorint(n)
sympy = _sympy_shim()

def subgroup_set(p, n, g=None):
    if g is None:
        g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    return S

import numpy as _np

def eta(p, S, b, expcache):
    s = 0j
    for x in S:
        s += expcache[(b * x) % p]
    return s

def worst_period(p, n, g, expcache=None):
    """M = max_{b != 0} ||eta_b(mu_n)||, EXACT.  We sweep one representative per mu_n-coset
    (m = (p-1)/n reps): eta_{c b}(mu_n) = eta_b(mu_n) for c in mu_n (reindex), so coset reps
    cover all distinct magnitudes.  Fully vectorized numpy (batched over reps to cap memory)."""
    S = _np.array(subgroup_set(p, n, g), dtype=_np.int64)
    m = (p - 1) // n
    twopi_over_p = 2.0 * math.pi / p
    # coset reps: 1, g^n, g^{2n}, ... (m of them) = powers of (g^n) -- but eta_{rep} magnitude
    # is invariant under rep -> c*rep (c in mu_n), so reps = g^0, g^1, ..., g^{m-1} also work and
    # are simpler; use rep_k = g^k for k=0..m-1 (these hit every mu_n-coset exactly once).
    reps = _np.empty(m, dtype=_np.int64)
    r = 1
    for k in range(m):
        reps[k] = r
        r = (r * g) % p
    best = 0.0
    best_b = 1
    # batch reps to keep the (batch x n) matrix small
    batch = max(1, min(m, (1 << 22) // max(1, n)))
    for start in range(0, m, batch):
        chunk = reps[start:start + batch]            # (B,)
        prod = (chunk[:, None] * S[None, :]) % p      # (B, n)
        ph = prod.astype(_np.float64) * twopi_over_p
        re = _np.cos(ph).sum(axis=1)
        im = _np.sin(ph).sum(axis=1)
        mag = _np.hypot(re, im)                        # (B,)
        j = int(_np.argmax(mag))
        if mag[j] > best:
            best = float(mag[j])
            best_b = int(chunk[j])
    return best, best_b, S

def analyze(p, levels):
    g = primitive_root(p)
    expcache = None
    rows = []
    prevM2 = None
    for i in levels:
        n = 1 << i
        if (p - 1) % n != 0:
            rows.append((i, n, None))
            continue
        m = (p - 1) // n
        M, bstar, S = worst_period(p, n, g, expcache)
        M2 = M * M
        gaussian2 = n * math.log(m) if m > 1 else float('nan')
        row = {
            'i': i, 'n': n, 'm': m, 'oddpart': m // (m & -m) if m > 0 else 0,
            'M': M, 'M2': M2, 'bstar': bstar,
            'c_i': (M2 / gaussian2 - 1) if (m > 1) else float('nan'),  # D3
        }
        if prevM2 is not None and prevM2 > 0:
            rho = M2 / (2 * prevM2)
            row['rho'] = rho            # D1
            row['excess'] = rho - 1     # D1
            row['d_i'] = math.log2(rho) # D4
        prevM2 = M2
        rows.append((i, n, row))
    return rows

def main():
    # primes: need (p-1) divisible by 2^i for the deepest level we enumerate, and
    # odd_part((p-1)/n) > 1 at the deepest level (exclude Fermat 2-power-fully-dyadic trap).
    # Enumerable: n up to 2^9 = 512 cheap; worst-period sweep is m=(p-1)/n reps each O(n).
    # (p, min_level, max_level).  Cost per level = m*n = (p-1) numpy reductions; we cap the
    # shallow (huge-m) levels by starting at min_level, and push max_level as deep as 2^i | p-1.
    # Going DEEP (large i) is what the decay test needs; we get depth from rich-v2 primes.
    cases = [
        (12289,   2, 12),   # p-1 = 2^12 * 3       -> tower i=2..12 (full, cheap, p small)
        (40961,   2, 13),   # p-1 = 2^13 * 5       -> i=2..13
        (786433,  5, 18),   # p-1 = 2^18 * 3       -> i=5..18 (deepest tower)
        (3145729, 6, 20),   # p-1 = 2^20 * 3       -> i=6..20 (even deeper, p still moderate)
        (65537,   2, 16),   # FERMAT p-1=2^16      -> degenerate control (odd cofactor 1)
    ]
    print("=" * 100)
    print("T13: per-level deviation delta_i of the 2-adic Gauss-period cocycle (EXACT)")
    print("=" * 100)
    for p, minlev, maxlev in cases:
        fac = sympy.factorint(p - 1)
        v2 = fac.get(2, 0)
        odd = (p - 1) >> v2
        tag = " [FERMAT/degenerate, odd cofactor=1]" if odd == 1 else ""
        print(f"\n### p = {p},  p-1 = 2^{v2} * {odd}{tag}  (tower levels {minlev}..{min(maxlev, v2)})")
        sys.stdout.flush()
        levels = list(range(minlev, min(maxlev, v2) + 1))
        rows = analyze(p, levels)
        print(f"  {'i':>2} {'n':>5} {'m':>9} {'M':>10} {'rho=M2/2M2_':>11} "
              f"{'excess':>9} {'d_i=log2rho':>11} {'c_i(M2/nlnm-1)':>14}")
        for i, n, row in rows:
            if row is None:
                continue
            rho = row.get('rho', float('nan'))
            ex = row.get('excess', float('nan'))
            di = row.get('d_i', float('nan'))
            print(f"  {row['i']:>2} {row['n']:>5} {row['m']:>9} {row['M']:>10.4f} "
                  f"{rho:>11.4f} {ex:>9.4f} {di:>11.4f} {row['c_i']:>14.4f}")
        # decay test: fit d_i vs 1/i and vs const on the deep tail
        di_seq = [(row['i'], row['d_i']) for i, n, row in rows
                  if row is not None and 'd_i' in row and not math.isnan(row['d_i'])]
        if len(di_seq) >= 3:
            tail = di_seq[len(di_seq)//2:]
            # is d_i decaying? compare first-half-tail avg to last-quarter
            print(f"     decay check (d_i): seq = {[f'{d:.3f}' for _,d in di_seq]}")
            # ratio of consecutive d_i: if O(1/i) then d_i * i ~ const
            prod = [(i, d * i) for i, d in di_seq]
            print(f"     d_i * i (const if O(1/i)): {[f'{v:.3f}' for _,v in prod]}")
            # cumulative sum of d_i = total log2 excess over pure doubling
            cum = 0.0
            cums = []
            for i, d in di_seq:
                cum += d
                cums.append((i, cum))
            print(f"     cumulative Sum d_i (=log2 of total overshoot factor): "
                  f"{[f'{c:.3f}' for _,c in cums]}")

if __name__ == "__main__":
    main()
