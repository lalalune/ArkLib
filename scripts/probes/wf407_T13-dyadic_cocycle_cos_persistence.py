"""
wf407 / T13-dyadic : the cocycle multiplier r_i, its excess over Gaussian, and the
phase-alignment persistence (389-T03 connection).

This is the SHARP companion to wf407_T13-dyadic_deviation_decay.py.  It computes, EXACTLY,
at every tower level i (subgroup mu_{2^i}):

  - the worst frequency b*_i and worst period M_i = ||eta_{b*}(mu_{2^i})||
  - the two level-(i-1) child periods at that SAME b*:
        A = eta_{b*}(mu_{2^{i-1}}),   B = eta_{b* z}(mu_{2^{i-1}})   (z gen of mu_{2^i})
    so that  eta_{b*}(mu_{2^i}) = A + B   (untwisted) EXACTLY (Sweep_A12 split identity).
  - the cocycle multiplier  r_i := M_i / max(|A|,|B|)   in [1, 2]   (worst-period growth factor)
    and  rho_i := M_i^2 / (2 M_{i-1}^2)  (the doubling ratio).
  - the COHERENCE / phase alignment  cos_i := Re(A conj B) / (|A| |B|)  (the 389-T03 object).
  - PERSISTENCE: does cos stay +1 one level down at the same b*?  (389-T03: "cos=1 persists
    one level down")  -- we track cos at level i AND the child-alignment at level i-1 for b*_i.

THE DECISION (per the census row):
  delta_i := the per-level cocycle EXCESS over the pure-Gaussian doubling.  Two exact forms:
     (a)  delta_i^cross := 2 Re(A conj B) / (|A|^2 + |B|^2)  in [-1, 1]
          (the normalized cross term: rho_i = (|A|^2+|B|^2 + 2Re(A conj B)) / (2 M_{i-1}^2);
           when A,B are the worst children, |A|^2+|B|^2 ~ 2 M_{i-1}^2 and rho_i ~ 1 + delta_i^cross.)
     (b)  d_i := log2(rho_i)   (cumulative Sum d_i = log2 of total overshoot vs pure doubling)
  Decay test:  is delta_i (or d_i) ~ C/i (O(1/i)),  slower,  or non-decaying (-> const)?
     * non-decaying const c>0  => M_a^2 >= 2^a 2^{ca} = n^{1+c}  => POWER overshoot = FATAL.
     * O(1/i)                  => Sum ~ C log a = C loglog n     => only polylog = floor SURVIVES.

We exclude the Fermat odd_part=1 trap (p=65537) as a degenerate control only.
"""
import cmath, math, sys
import numpy as np

def factorint(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def primitive_root(p):
    phi = p - 1; facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in facs):
            return g
    raise RuntimeError

def subgroup(p, n, g):
    h = pow(g, (p - 1) // n, p); S = []; x = 1
    for _ in range(n):
        S.append(x); x = (x * h) % p
    return np.array(S, dtype=np.int64)

def eta(p, S, b):
    ph = ((b * S) % p).astype(np.float64) * (2 * math.pi / p)
    return np.cos(ph).sum() + 1j * np.sin(ph).sum()

def worst_b(p, n, g):
    """worst frequency b* and M = ||eta_{b*}|| over one rep per mu_n-coset."""
    S = subgroup(p, n, g); m = (p - 1) // n
    reps = np.empty(m, dtype=np.int64); r = 1
    for k in range(m):
        reps[k] = r; r = (r * g) % p
    best = -1.0; bb = 1
    batch = max(1, min(m, (1 << 22) // max(1, n)))
    for s in range(0, m, batch):
        ch = reps[s:s + batch]
        ph = ((ch[:, None] * S[None, :]) % p).astype(np.float64) * (2 * math.pi / p)
        mag = np.hypot(np.cos(ph).sum(1), np.sin(ph).sum(1))
        j = int(np.argmax(mag))
        if mag[j] > best: best = float(mag[j]); bb = int(ch[j])
    return bb, best

def analyze(p, minlev, maxlev):
    g = primitive_root(p)
    v2 = factorint(p - 1).get(2, 0)
    maxlev = min(maxlev, v2)
    rows = []
    prevM2 = None
    for i in range(minlev, maxlev + 1):
        n = 1 << i
        bstar, M = worst_b(p, n, g)
        M2 = M * M
        # children at level i-1 for the SAME b*: A = eta_b*(mu_{n/2}), B = eta_{b* z}(mu_{n/2})
        # z = generator of mu_n (order n) => z = g^{(p-1)/n}.  mu_{n/2} = <z^2>.
        z = pow(g, (p - 1) // n, p)
        Shalf = subgroup(p, n // 2, g)
        A = eta(p, Shalf, bstar)
        B = eta(p, Shalf, (bstar * z) % p)
        absA, absB = abs(A), abs(B)
        cross = (A * B.conjugate()).real
        cos_i = cross / (absA * absB) if absA * absB > 1e-12 else float('nan')
        # exact check: A+B should equal eta_b*(mu_n)
        chk = abs((A + B) - eta(p, subgroup(p, n, g), bstar))
        m = (p - 1) // n
        row = dict(i=i, n=n, m=m, M=M, M2=M2, bstar=bstar,
                   absA=absA, absB=absB, cos=cos_i,
                   r_i=M / max(absA, absB) if max(absA, absB) > 0 else float('nan'),
                   delta_cross=2 * cross / (absA**2 + absB**2) if (absA**2+absB**2) > 0 else float('nan'),
                   split_resid=chk,
                   c_i=(M2 / (n * math.log(m)) - 1) if m > 1 else float('nan'))
        if prevM2:
            row['rho'] = M2 / (2 * prevM2)
            row['d_i'] = math.log2(row['rho'])
        prevM2 = M2
        rows.append(row)
    return rows, v2

def main():
    cases = [
        (12289,   2, 12),
        (40961,   2, 13),
        (786433,  5, 18),
        (3145729, 6, 20),
        (65537,   2, 16),   # Fermat degenerate control
    ]
    print("=" * 110)
    print("T13: cocycle multiplier r_i, cross-term deviation delta_i, phase-alignment cos_i (EXACT)")
    print("=" * 110)
    all_di = {}
    for p, lo, hi in cases:
        v2 = factorint(p - 1).get(2, 0)
        odd = (p - 1) >> v2
        tag = "  [FERMAT degenerate control, odd_part=1]" if odd == 1 else ""
        print(f"\n### p={p}  p-1=2^{v2}*{odd}{tag}")
        sys.stdout.flush()
        rows, v2 = analyze(p, lo, hi)
        print(f"  {'i':>2} {'n':>6} {'m':>8} {'M':>9} {'r_i':>6} {'rho':>6} "
              f"{'d_i':>7} {'cos_i':>7} {'delta_x':>8} {'c_i':>7} {'splitres':>9}")
        for r in rows:
            print(f"  {r['i']:>2} {r['n']:>6} {r['m']:>8} {r['M']:>9.3f} "
                  f"{r['r_i']:>6.3f} {r.get('rho', float('nan')):>6.3f} "
                  f"{r.get('d_i', float('nan')):>7.3f} {r['cos']:>7.3f} "
                  f"{r['delta_cross']:>8.3f} {r['c_i']:>7.3f} {r['split_resid']:>9.1e}")
        di = [(r['i'], r['d_i']) for r in rows if 'd_i' in r and not math.isnan(r['d_i'])]
        if di and odd > 1:
            all_di[p] = di
            print(f"     d_i sequence:        {[f'{d:+.3f}' for _,d in di]}")
            print(f"     d_i * i (const if 1/i): {[f'{d*i:+.3f}' for i,d in di]}")
            cum = 0; cums = []
            for i, d in di:
                cum += d; cums.append(cum)
            print(f"     cumulative Sum d_i:  {[f'{c:+.3f}' for c in cums]}")
            print(f"     cos_i sequence:      "
                  f"{[f'{r['cos']:+.2f}' for r in rows]}")
    # cross-prime decay verdict
    print("\n" + "=" * 110)
    print("DECAY VERDICT")
    print("=" * 110)
    for p, di in all_di.items():
        if len(di) < 4: continue
        # is d_i decaying? Linear regression of |d_i| vs 1/i and vs const.
        xs = np.array([i for i, _ in di], dtype=float)
        ys = np.array([abs(d) for _, d in di], dtype=float)
        # tail (deep levels) average vs head average
        head = ys[:len(ys)//2].mean()
        tail = ys[len(ys)//2:].mean()
        # fit d_i ~ C/i  => d_i*i ~ C const ; check variance of d_i*i over tail
        prod = ys * xs
        prod_tail = prod[len(prod)//2:]
        print(f"  p={p}: |d_i| head_avg={head:.4f} tail_avg={tail:.4f} "
              f"(decaying={'YES' if tail < 0.6*head else ('slow' if tail<head else 'NO')}); "
              f"|d_i|*i tail mean={prod_tail.mean():.3f} std={prod_tail.std():.3f} "
              f"(flat=>O(1/i)); deep |d_i|={ys[-1]:.4f}")

if __name__ == "__main__":
    main()
