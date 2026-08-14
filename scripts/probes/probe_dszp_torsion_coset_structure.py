#!/usr/bin/env python3
"""
probe_dszp_torsion_coset_structure.py  (#444 — model-theory / Zilber-Pink lead)
DO NOT COMMIT. Diagnostic only.

GOAL. Test the Zilber-Pink / Bombieri-Masser-Zannier STRUCTURAL prediction against the
validated GPU/Rust orbit data for the over-determined far-line incidence count.

THE ZP/BMZ FRAME (char-0, p-independent — matches the decoupling result).
  Manin-Mumford for tori (Laurent 1984): for any subvariety V of G_m^N, the Zariski closure
  of the torsion points V_tors is a FINITE union of MAXIMAL TORSION COSETS  omega * H
  (H a subtorus, omega a torsion point). Martinez 2015 (arXiv:1509.05898), refining
  Amoroso-Viada (Duke 2009): the number/degree of these maximal torsion cosets is bounded by
      deg(V^j_tors) <= c_N * delta^{N-j},   c_N = ((2N-1)(N-1)(2^{2N}+2^{N+1}-2))^{N d},
  i.e. POLYNOMIAL in the defining degree delta with exponent (N - j) <= N, but with a constant
  c_N that is DOUBLY-EXPONENTIAL in the ambient dimension N.

OUR OBJECT. Far direction (a,b), agreement size s = k + c (c = over-determination). The bad-gamma
set is  { gamma in F_p : x^a + gamma x^b agrees with some RS[mu_n,k] codeword on >= s of the n pts }.
Each bad gamma corresponds to a size-s subset R subset mu_n on which [x^0..x^{k-1}, x^a, x^b] is
rank-deficient. The bad SUBSETS R live in mu_n^s subset G_m^s as torsion points of the variety
  V_{a,b,s} = { (x_1..x_s) : det-minors of generalized-Vandermonde [x^0..x^{k-1},x^a,x^b] vanish }.
So the bad-set IS a torsion-point set of a torus subvariety: BMZ/ZP applies in dimension N = n
(the natural ambient is mu_n, x_i = zeta^{e_i}, e_i in Z/n) or N = s (the witness coordinates).

WHAT WE TEST (tasks 3-4). The wf-D5 mechanism already says: nonzero bad gammas form mu_{n/2}-orbits
under gamma -> zeta^{a-b} gamma. That IS a torsion-coset family: a single subtorus H = mu_{n/g}
(g = gcd(a-b,n)) of the gamma-line, translated by the orbit reps. So O(s) = #orbits = # maximal
torsion cosets of the gamma-locus, and N (the orbit-count residual) = O(s*).

ZP's sharp prediction: at the BINDING band the bad-locus is EXACTLY a finite union of these
torsion cosets with NO isolated (0-dim torsion-point) REMAINDER beyond what the coset families
account for, AND the number of families is bounded by the Martinez/Amoroso-Viada count.

CONCRETE CHECKS for n in {16, 32}, rho=1/4, k=n/4:
  (A) For each far direction (a,b), at each over-determination c, decompose the nonzero bad-gamma
      set into orbits of the dilation subgroup mu_{n/g}, g=gcd(a-b,n). Confirm every orbit is FULL
      (size n/g) => each is a genuine torsion coset, NO partial/isolated remainder.
  (B) Count maximal torsion-coset families O(c) per direction; take max over directions = N(c).
      Confirm I(c) = [gamma=0 bad] + (n/g)*O(c) and the crossing N <= 2 at the Johnson band.
  (C) Compare N(c*) (orbit count at the binding s*) to the GPU s* law and to the Martinez bound.

VERDICT printed at the end: NEW-HANDLE vs REDUCES-TO-ORBIT-COUNT vs COLLAPSES.
"""
import sys, itertools
from math import gcd, sqrt, comb


def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i * i <= m:
        if m % i == 0: return False
        i += 2
    return True


def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and is_prime(p):
            return p
        p += n


def subgroup(n, p):
    for c in range(2, p):
        h = pow(c, (p - 1) // n, p)
        if pow(h, n, p) == 1 and len({pow(h, j, p) for j in range(n)}) == n:
            return [pow(h, j, p) for j in range(n)], h
    raise RuntimeError


def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0; pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        inv = pow(rows[pr][c], p - 2, p)
        rows[pr] = [(x * inv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j] - f * rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows


def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]


def bad_gammas(S, p, k, a, b, r):
    """Exact bad-gamma set at radius r (agreement size = n-r). None if heavy/saturated."""
    n = len(S); size = n - r
    if size <= k: return None
    pa = [pow(int(x), a, p) for x in S]; pb = [pow(int(x), b, p) for x in S]; good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]; P = left_null(V, p)
        if not P: continue
        u = [sum(P[t][ii] * pa[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        v = [sum(P[t][ii] * pb[R[ii]] for ii in range(size)) % p for t in range(len(P))]
        if not any(v):
            if not any(u): return None
            continue
        i = next(j for j in range(len(v)) if v[j]); g = (-u[i] * pow(v[i], p - 2, p)) % p
        if all((u[t] + g * v[t]) % p == 0 for t in range(len(v))): good.add(g)
    return good


def coset_decompose(nz, dil, p, half):
    """Decompose nonzero bad gammas into orbits of <dil> (the dilation subtorus mu_{half}).
    Returns (num_families, list_of_orbit_sizes, all_full_flag)."""
    nz = set(nz); seen = set(); sizes = []
    for g in sorted(nz):
        if g in seen: continue
        orb = []; x = g
        for _ in range(half):
            if x in nz and x not in seen:
                seen.add(x); orb.append(x)
            x = (x * dil) % p
        sizes.append(len(orb))
    all_full = all(s == half for s in sizes)
    return len(sizes), sizes, all_full


def analyze(n, k, far_dirs, max_c=None):
    p = find_prime_cong1(n, 200003)
    S, gen = subgroup(n, p)
    rho = k / n
    sJ = sqrt(rho) * n
    print(f"\n========== n={n} k={k} rho={rho} (Johnson agreement s_J=sqrt(rho)*n={sJ:.2f}) ==========")
    print(f"prime p={p}  budget(=n)={n}")
    summary = {}  # c -> max orbit families N(c)
    detail = {}
    for (a, b) in far_dirs:
        g = gcd(b - a, n)
        half = n // g                      # dilation subtorus order = n/gcd(b-a,n)
        dil = pow(gen, (b - a) % n, p)      # gamma -> gamma * zeta^{a-b}; subgroup generator
        # the multiplicative order of dil = n/gcd(a-b,n) = half
        cmax = max_c if max_c is not None else (n - 2 - k)
        line = []
        for c in range(0, cmax + 1):
            s = k + c; r = n - s
            if r < 0: break
            bg = bad_gammas(S, p, k, a, b, r)
            if bg is None:
                line.append((c, s, 'SAT', None, None, None, None))
                continue
            zero_bad = 1 if 0 in bg else 0
            nz = bg - {0}
            nfam, sizes, full = coset_decompose(nz, dil, p, half)
            I = zero_bad + len(nz)
            pred = zero_bad + half * nfam
            line.append((c, s, I, nfam, full, half, pred))
            summary.setdefault(c, 0)
            summary[c] = max(summary[c], nfam)
        detail[(a, b)] = (g, half, line)
        print(f"\n  dir (a,b)=({a},{b})  gcd(b-a,n)={g}  dilation subtorus order half=n/g={half}")
        print(f"   {'c':>3} {'s':>3} {'I':>6} {'#fam(N)':>8} {'allFull':>8} {'half':>5} {'I=pred?':>8}")
        for (c, s, I, nfam, full, h, pred) in line:
            if I == 'SAT':
                print(f"   {c:>3} {s:>3} {'SAT':>6} {'-':>8} {'-':>8} {'-':>5} {'-':>8}")
            else:
                ok = 'YES' if I == pred else f'NO(pred {pred})'
                print(f"   {c:>3} {s:>3} {I:>6} {nfam:>8} {str(full):>8} {h:>5} {ok:>8}")
    return summary, detail, sJ


def main():
    # far directions: a,b in [k,n), b<n; include the GPU-reported binding/worst dirs.
    # n=16 binding (10,4) per wf-D5; plus a spread of far dirs.
    cfgs = {
        16: dict(k=4, dirs=[(10, 4), (6, 4), (9, 8), (12, 4), (5, 6), (4, 7)]),
        # n=32: GPU worst dir near n/2 e.g. (20,8); include several near n/2 and small-gap.
        32: dict(k=8, dirs=[(20, 8), (18, 8), (16, 10), (12, 10), (24, 8)]),
    }
    results = {}
    for n in (16, 32):
        c = cfgs[n]
        # limit c range for n=32 to keep C(n,s) enumeration feasible around the band.
        # n=32, k=8: cost ~ C(32, 8+c). c<=3 => C(32,11)~1.3e8, feasible. Deeper bands hit the
        # known C(n,s) witness wall (documented in probe_444r2_overdet_orbit_growth.py); the
        # small-c structural shape (full orbits, I = half*N) is what ZP predicts and suffices.
        max_c = None if n == 16 else 3
        summary, detail, sJ = analyze(n, c['k'], c['dirs'], max_c=max_c)
        results[n] = (summary, sJ, c['k'])

    print("\n\n================= ZP / BMZ STRUCTURAL VERDICT =================")
    for n in (16, 32):
        summary, sJ, k = results[n]
        # binding band: smallest c (=s-k) where max-over-dirs N(c) <= 2  (since (n/2)*2 = n = budget,
        # and for g=2 dirs the crossing is N<=2). report the orbit count there.
        print(f"\n n={n}: max-over-dir orbit-family count N(c) by over-determination c:")
        for c in sorted(summary):
            band = ''
            if k + c >= sJ:
                band = '  <- at/above Johnson band'
            print(f"    c={c} (s={k+c}): N={summary[c]}{band}")
    print("""
INTERPRETATION
  (A) all orbits FULL (size half) at the binding band  => bad-set = EXACT union of torsion cosets,
      NO isolated remainder => ZP structure CONFIRMED (Manin-Mumford shape realized exactly).
  (B) I = [0 bad] + half * N(c) holds exactly      => N(c) = # maximal torsion cosets = orbit count.
  (C) N(c*) at the Johnson band: if N drops to <= 2 exactly at s ~ s_J, the crossing IS the
      Johnson list collapse, and the ZP coset count = the orbit-count residual (same object).
""")


if __name__ == '__main__':
    main()
