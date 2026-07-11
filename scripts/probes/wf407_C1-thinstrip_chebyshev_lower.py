#!/usr/bin/env python3
"""
wf407 / C1-thinstrip — the THIN-STRIP LOWER BRACKET past Johnson via Chebyshev /
Paley-Zygmund at the census M3 variance.

THE THREAD (K3 thin-strip lower bracket):
  Push a delta* LOWER bound past Johnson into the window (1-sqrt(rho),
  1-sqrt(rho)+c/log n) using Chebyshev at the census M3 variance.  Concretely:
  the second-moment (Paley-Zygmund) LOWER bound on the WORST-CASE list size is

        max_u L(u)  >=  M2 / M1        (M_r = sum_u L(u)^r over received words u)

  because  max_u L(u) * sum_u L(u) >= sum_u L(u)^2.  The cube-over-square ladder
  gives a refined lower bound  max_u L(u) >= M3 / M2  (Cauchy-Schwarz on the
  sequence L(u)), and M2^2/M3 <= max as well.  These are the ONLY directions in
  which a moment can FORCE a large worst-case list (= a delta* LOWER bracket).

  The QUESTION (the verdict to land):
    (1) Compute the M3 variance on the strip for smooth mu_n at n=16,32 EXACTLY.
    (2) Does this second-moment LOWER bound exceed the JOHNSON prediction at a
        radius the Johnson bound cannot reach (strip just past 1-sqrt(rho))?
    (3) Reconcile the floor candidates: WB (1-rho)/2 vs half-Johnson vs census.

KEY PRIOR ART:
  * O120/O122: M1 and M2 of the agreement spectrum are DOMAIN-INDEPENDENT closed
    forms.  M3 is the first domain-dependent moment.
  * O133: M3 IS domain-dependent but |Delta M3|/M3 ~ q^{-4} (tiny).
  * O173: the 2nd-moment pair-sum UPPER route gives Var ~ E^2 (Poisson), blind to
    the worst line.  This probe is the COMPLEMENTARY LOWER (Paley-Zygmund) side.

L_w(u) = #{ p in RS[F_q,D,k] : hamming(p,u) <= w }  (cumulative agreement spectrum).

MOMENTS VIA CODEWORD TUPLES (no q^n enumeration):
  M1 = sum_c Vol(c,w)                        = q^k * V(w)
  M2 = sum_{c1,c2} |Ball(c1)∩Ball(c2)|       (pairwise)
  M3 = sum_{c1,c2,c3} |Ball(c1)∩Ball(c2)∩Ball(c3)|   (triples)
  The r-ball intersection over F_q^n FACTORS per coordinate (the balls are
  product/Hamming), so |∩ Ball(c_i,w)| is computed by a small DP over coordinates
  tracking the per-codeword running disagreement counts -- exact, polynomial in n,
  with at most (w+1)^r states.  This sees the EXACT domain via the codeword
  evaluation pattern (the distance/coincidence structure of c1,c2,c3 on D).

All arithmetic is exact Python ints.  No sampling on any verdict.
"""

from math import comb, isqrt
from fractions import Fraction
import itertools, sys


def is_prime(m):
    if m < 2: return False
    for p in range(2, isqrt(m) + 1):
        if m % p == 0: return False
    return True


def smooth_subgroup(p, n):
    assert (p - 1) % n == 0, f"n={n} must divide p-1={p-1}"
    def order(g):
        x = 1
        for k in range(1, p):
            x = (x * g) % p
            if x == 1:
                return k
        return p
    g = next(c for c in range(2, p) if order(c) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x); x = (x * h) % p
    return sorted(set(H))


def all_codewords(p, D, k):
    cws = []
    for coeffs in itertools.product(range(p), repeat=k):
        cws.append(tuple(sum(coeffs[i] * pow(x, i, p) for i in range(k)) % p
                         for x in D))
    return cws


# --------------------------------------------------------------------------
# Exact r-fold ball-intersection volume over F_q^n via per-coordinate DP.
# State = tuple of running disagreement counts (one per center), each <= w.
# For each coordinate i, a received symbol y_i in F_q either equals each center's
# symbol or not; we bucket the q choices by the agreement pattern of the r centers
# at coordinate i (a function of the symbols c_1[i],...,c_r[i]).
# Number of distinct symbols among c_1[i..],..,c_r[i] partitions q into groups;
# each group g (a value v) contributes "agrees with exactly the centers whose
# symbol is v" with multiplicity = (count of that value), plus "agrees with none"
# with multiplicity q - (#values present).  We enumerate the <=2^r agreement masks.
# --------------------------------------------------------------------------
def intersect_volume(centers, w, q):
    n = len(centers[0])
    r = len(centers)
    # initial state: all zero disagreements, count 1
    from collections import defaultdict
    states = {(0,) * r: 1}
    for i in range(n):
        syms = [c[i] for c in centers]
        # group center-indices by symbol value at this coordinate
        valgroups = defaultdict(list)
        for idx, v in enumerate(syms):
            valgroups[v].append(idx)
        # transitions: choosing y_i = some value present (agree with that group's
        # centers, disagree with the rest) OR y_i = a value not among syms
        # (disagree with all).
        # build list of (agree_mask_as_set_of_indices, multiplicity)
        trans = []
        present_values = len(valgroups)
        for v, idxs in valgroups.items():
            # exactly 1 symbol value v: y_i=v agrees with idxs, disagrees others
            trans.append((set(idxs), 1))
        # y_i = any of the q - present_values other symbols: disagree with all
        other_mult = q - present_values
        if other_mult > 0:
            trans.append((set(), other_mult))
        new_states = defaultdict(int)
        for st, cnt in states.items():
            for agree, mult in trans:
                ns = list(st)
                ok = True
                for j in range(r):
                    if j not in agree:
                        ns[j] += 1
                        if ns[j] > w:
                            ok = False
                            break
                if ok:
                    new_states[tuple(ns)] += cnt * mult
        states = dict(new_states)
        if not states:
            return 0
    return sum(states.values())


def exact_moments_via_tuples(p, D, k, w):
    """EXACT M1,M2,M3 (and maxL bound via triple search is NOT done here; max is
    approximated below).  Uses codeword tuples; cost q^k for M1, q^{2k}/2 for M2,
    q^{3k}/6 for M3 with symmetry."""
    n = len(D)
    cws = all_codewords(p, D, k)
    Q = len(cws)
    # M1
    M1 = 0
    vols = []
    for c in cws:
        v = intersect_volume([c], w, p)
        vols.append(v)
        M1 += v
    # M2 = sum over ordered pairs
    M2 = 0
    for i in range(Q):
        M2 += vols[i]  # i==j diagonal? no: ordered pair (i,i) volume = vols[i]
        for j in range(i + 1, Q):
            v = intersect_volume([cws[i], cws[j]], w, p)
            M2 += 2 * v
    # M3 = sum over ordered triples
    M3 = 0
    for i in range(Q):
        M3 += vols[i]                      # (i,i,i)
        for j in range(i + 1, Q):
            vij = intersect_volume([cws[i], cws[j]], w, p)
            M3 += 3 * vij                  # (i,i,j),(i,j,i),(j,i,i) and perms with one repeat
            M3 += 3 * vij                  # (j,j,i),(j,i,j),(i,j,j)
            for l in range(j + 1, Q):
                vijl = intersect_volume([cws[i], cws[j], cws[l]], w, p)
                M3 += 6 * vijl
    return M1, M2, M3, cws


def exact_max_full(p, D, k, w):
    """True max_u L_w(u) by enumerating received words -- only for tiny p^n."""
    n = len(D)
    cws = all_codewords(p, D, k)
    if p ** n > 4_000_000:
        return None
    mx = 0
    for u in itertools.product(range(p), repeat=n):
        L = sum(1 for c in cws if sum(1 for i in range(n) if c[i] != u[i]) <= w)
        if L > mx: mx = L
    return mx


# --------------------------------------------------------------------------
# Closed forms (domain-INDEPENDENT) for M1, M2.
# --------------------------------------------------------------------------
def ball_volume(n, w, q):
    return sum(comb(n, j) * (q - 1) ** j for j in range(0, w + 1))


def mds_weight_enum(n, kp, q):
    dmin = n - kp + 1
    A = [0] * (n + 1); A[0] = 1
    for ww in range(dmin, n + 1):
        s = 0
        for j in range(0, ww - dmin + 1):
            term = comb(ww, j) * (q ** (ww - dmin + 1 - j) - 1)
            s += term if j % 2 == 0 else -term
        A[ww] = comb(n, ww) * s
    return A


def icap(n, d, w, q):
    if d == 0:
        return ball_volume(n, w, q)
    total = 0
    for t in range(0, (n - d) + 1):
        if t > w: break
        off = comb(n - d, t) * (q - 1) ** t
        s = 0
        for e in range(0, d + 1):
            if t + e > w: break
            qe = (q - 2) ** e if (q - 2) > 0 else (1 if e == 0 else 0)
            if qe == 0: continue
            rem = d - e; ub = w - t - e
            for b in range(0, rem + 1):
                if b > ub: break
                a = rem - b
                if a > ub: continue
                s += comb(d, e) * comb(d - e, b) * qe
        total += off * s
    return total


def M1_closed(n, k, w, q):
    return q ** k * ball_volume(n, w, q)


def M2_closed(n, k, w, q):
    A = mds_weight_enum(n, k, q)
    s = sum(A[d] * icap(n, d, w, q) for d in range(0, n + 1) if A[d])
    return q ** k * s


def johnson_cap(n, k, w):
    a = n - w; b = k - 1
    denom = a * a - n * b
    if denom <= 0:
        return None
    return Fraction(n * n, denom)


def johnson_radius(n, k):
    b = k - 1; w = 0
    while w < n:
        a = n - (w + 1)
        if a * a <= n * b: break
        w += 1
    return w


def f2(x):
    try:
        return float(x)
    except Exception:
        return float("nan")


def banner(s):
    print("\n" + "=" * 78); print(s); print("=" * 78)


if __name__ == "__main__":
    banner("PART A -- verify intersect_volume DP + closed M1,M2 (exact)")
    for (p, n, k) in [(7, 6, 2), (11, 5, 2)]:
        H = smooth_subgroup(p, n) if (p - 1) % n == 0 else sorted(range(1, n + 1))
        for w in [0, 1, 2, n // 2]:
            M1, M2, M3, _ = exact_moments_via_tuples(p, H, k, w)
            m1c, m2c = M1_closed(n, k, w, p), M2_closed(n, k, w, p)
            ok = (M1 == m1c and M2 == m2c)
            mx = exact_max_full(p, H, k, w)
            print(f"  p={p} n={n} k={k} w={w}: M1={M1} M2={M2} M3={M3} maxL={mx} "
                  f"[{'OK' if ok else f'MISMATCH M1:{M1==m1c} M2:{M2==m2c}'}]")

    banner("PART B -- subgroup vs random: M3 + moment-ladder LOWER bounds vs max")
    import random
    for (p, n, k) in [(11, 5, 2), (7, 6, 2), (13, 6, 2), (13, 6, 3)]:
        if (p - 1) % n != 0:
            print(f"  (skip p={p} n={n}: {n} does not divide {p-1})"); continue
        H = smooth_subgroup(p, n)
        random.seed(7)
        R = sorted(random.sample(range(p), n))
        print(f"\n  p={p} n={n} k={k}: H={H}  R={R}")
        for w in range(max(0, n - k - 2), n):
            M1H, M2H, M3H, _ = exact_moments_via_tuples(p, H, k, w)
            M1R, M2R, M3R, _ = exact_moments_via_tuples(p, R, k, w)
            pzH = Fraction(M2H, M1H); pzR = Fraction(M2R, M1R)
            m32H = Fraction(M3H, M2H); m32R = Fraction(M3R, M2R)   # M3/M2 <= max
            mxH = exact_max_full(p, H, k, w)
            mxR = exact_max_full(p, R, k, w)
            J = johnson_cap(n, k, w)
            jstr = f"{f2(J):.2f}" if J is not None else "PAST-J"
            print(f"   w={w} d={w/n:.3f} J<={jstr:6}| "
                  f"H: M3={M3H} PZ={f2(pzH):.3f} M3/M2={f2(m32H):.3f} max={mxH} | "
                  f"R: M3={M3R} PZ={f2(pzR):.3f} M3/M2={f2(m32R):.3f} max={mxR}")

    banner("PART C -- THE STRIP: PZ lower bound vs Johnson at prize-shaped q>>n")
    print("Paley-Zygmund worst-case lower bound  max_u L >= M2/M1  (DOMAIN-INDEP),")
    print("from Johnson radius up to capacity, q ~ n*2^128. Does PZ force max>=2")
    print("(i.e. a NONTRIVIAL list) at a radius the Johnson bound cannot reach?\n")
    for (n, k) in [(16, 8), (32, 16), (16, 4), (32, 8), (16, 2)]:
        q = (1 << 128) * n + 1
        rho = k / n
        wJ = johnson_radius(n, k)
        dJ = 1 - rho ** 0.5
        target = q ** (n - k); wcap = 0; V = 1
        while wcap < n:
            Vn = V + comb(n, wcap + 1) * (q - 1) ** (wcap + 1)
            if Vn > target: break
            V = Vn; wcap += 1
        print(f" n={n} k={k} rho={rho:.3f} | Johnson reach w<={wJ}(dJ~{dJ:.3f}) "
              f"| capacity w~{wcap}(dcap~{1-rho:.3f})")
        for w in range(wJ, min(wcap + 2, n) + 1):
            M1 = M1_closed(n, k, w, q); M2 = M2_closed(n, k, w, q)
            pz = Fraction(M2, M1); EL = Fraction(M1, q ** n)
            J = johnson_cap(n, k, w)
            jstr = f"{f2(J):.3f}" if J is not None else "PAST-J"
            tag = "<=J" if w <= wJ else ("PAST-J" if J is None else "")
            print(f"   w={w} d={w/n:.4f} {tag:7}| E[L]={f2(EL):.3e} "
                  f"PZ=M2/M1={f2(pz):.5f}  Johnson<= {jstr}")

    banner("PART D -- FLOOR RECONCILIATION: (1-rho)/2 vs half-Johnson vs census")
    print("  rho     (1-rho)/2   Johnson=1-sqrt(rho)   halfJ=Johnson/2   compare")
    for rho in [Fraction(1,2), Fraction(1,4), Fraction(1,8), Fraction(1,16)]:
        wb = (1 - rho) / 2; J = 1 - float(rho) ** 0.5; halfJ = J / 2
        rel = '>' if float(wb) > J else '<'
        print(f"  {f2(rho):.4f}  {f2(wb):.4f}      {J:.4f}             {halfJ:.4f}"
              f"          (1-rho)/2 {rel} Johnson")
    print("\n  O173: lower-window FULL closure lands at exactly (1-rho)/2 (2R<d_min")
    print("  => empty pair band => worst=avg, zero residual). Above it the moments")
    print("  give NO worst-case lower bracket (see PART C).")
    print("\ndone", flush=True)
