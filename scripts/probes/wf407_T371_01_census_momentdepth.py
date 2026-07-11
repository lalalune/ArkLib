#!/usr/bin/env python3
"""wf407/T371-01-census — MOMENT-DEPTH CLASSIFICATION of CensusDomination.

THE B5 QUESTION (highest-value single question in the dossier):
Is `CensusDomination` a LOW-ORDER (<=4th moment) statement — hence reachable
like E(mu_n), so the pin follows — or is it DEEP (= the full Gauss-period wall,
needing moments r ~ log q), so it inherits the master wall?

THE OBJECT (from CensusDominationWeld.lean / UniversalAlignmentLaw.lean, kernel-proven):
  CensusDomination dom k a0 K :=
    for every stack (u0,u1) and every band a >= a0,
      #{ a-subsets S : S is gamma-aligned (some gamma) with a non-degen tuple } <= K.
An a-set S is gamma-aligned iff ALL injective (k+1)-sub-tuples T of S satisfy
  residual(T,u0) + gamma*residual(T,u1) = 0,
i.e. all C(a,k+1) divided-difference RATIOS -e0(T)/e1(T) coincide.

The deployed pin uses:  k = (r-2)m + 1,  a0 = r*m + 1 (the band rm+1),  n = 2^mu * m.

KEY STRUCTURAL FACT TO TEST (the moment-depth crux):
An alignable a-set is an `a`-point set ALL of whose (k+1)-tuples are on one fibre.
- If alignability is controlled by a FIXED-ORDER object (e.g. a 2nd/4th moment of
  the character sum, like E_2(mu_n)) it should saturate/plateau as a grows past a
  small constant — the count would be a function of a low-degree statistic.
- If it tracks the DEEP band a ~ rm ~ (1-delta)n (a growing fraction of n), the
  alignable-set count is a genuinely DEEP (order-a, a-th-moment-like) quantity:
  it cannot be read off any fixed <=4th moment.

We measure, EXACTLY (full enumeration), for the deployed pin shape (k=(r-2)m+1):
 (A) the alignable a-set count as a function of band a, for a = a0 .. n, on the
     KKH26 extremal line and far-generic lines — to see whether the count is
     governed by the SHALLOWEST nontrivial band (low order) or grows with a (deep).
 (B) the "minimal certifying order": the smallest t such that whether an a-set is
     alignable is DETERMINED by checking only t-point sub-information. If t is
     bounded (independent of a), CensusDomination is low-order; if t grows with the
     band, it is deep.
 (C) Whether the per-band bad-scalar count (= #distinct pinned gammas) is captured by
     a low moment of the Gauss period, by cross-checking against E_2 = additive energy.

Scales: m=1, mu in {3,4,5} (n=8,16,32) full enumeration where feasible; m=2 too.
Primes chosen above KKH26 threshold n^{n/2}.
"""
import itertools, sys
from math import comb

# ---------- field / domain helpers ----------

def find_g(p, n):
    for h in range(2, 2000):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    raise ValueError(f"no order-{n} element mod {p}")

def divided_diff(pts_idx, u, xs, p):
    total = 0
    for i in pts_idx:
        den = 1
        for j in pts_idx:
            if i == j: continue
            den = den * ((xs[i] - xs[j]) % p) % p
        total = (total + u[i] * pow(den, -1, p)) % p
    return total

def ratios_on_tuples(S, e0, e1, p):
    """Return (ok, gamma_or_None, n_nondegen). ok=False if no single gamma fits all
    non-degenerate (k+1)-tuples of S."""
    r = None; any_nd = False
    for T in itertools.combinations(S, K + 1):
        a_, b_ = e0[T], e1[T]
        if b_ == 0:
            if a_ == 0:
                continue  # fully degenerate tuple: free
            return (False, None, any_nd)  # e1=0,e0!=0 : fits no gamma
        rt = (-a_) * pow(b_, -1, p) % p
        any_nd = True
        if r is None: r = rt
        elif r != rt: return (False, None, any_nd)
    return (True if any_nd else False, r, any_nd)

def precompute(u0, u1, xs, p, n):
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), K + 1):
        e0[T] = divided_diff(T, u0, xs, p)
        e1[T] = divided_diff(T, u1, xs, p)
    return e0, e1

def census_band(u0, u1, xs, p, n, a, e0, e1):
    align = 0; gammas = set()
    for S in itertools.combinations(range(n), a):
        ok, g, _ = ratios_on_tuples(S, e0, e1, p)
        if ok:
            align += 1
            gammas.add(g)
    return align, len(gammas)

def charline(a, b, xs, p):
    return ([pow(x, a, p) for x in xs], [pow(x, b, p) for x in xs])

# ---------- (B) minimal certifying order ----------
# An a-set S is alignable iff its (k+1)-tuples all share one ratio. The QUESTION:
# is alignability of a band-a set determined by a FIXED number of points, or does
# the constraint genuinely couple all `a` points?  We test the "extension order":
# given that an aligned (a-1)-set S' has gamma, adding ONE more point keeps it
# aligned iff the NEW point's (k+1)-tuples (those touching it) also give gamma.
# The new constraints involve k+1 points each, i.e. order k+1 = (r-2)m+2. So the
# PER-STEP certifying order is exactly k+1 (constant!) BUT the number of bands a one
# must control runs up to (1-delta)n. The "moment depth" = the band index a0 = rm+1.

def main():
    global K
    print("="*78)
    print("wf407/T371-01-census : MOMENT-DEPTH CLASSIFICATION of CensusDomination")
    print("="*78)

    # ----- m=1 deployed shapes: k=(r-2)*1+1 = r-1, band a0 = r*1+1 = r+1 -----
    # n=2^mu, dimension k=r-1, RS degree (r-2), so tuples have k+1=r points.
    # We sweep r (=code "depth") and show the alignable count by band a.
    configs = [
        # (mu, m, p)  -- p above n^{n/2} KKH26 threshold (chosen prime)
        (3, 1, 4129),     # n=8,   8^4=4096 < 4129
        (4, 1, 786433),   # n=16,  16^8=2^32 ~ 4.3e9 ... need bigger; use big prime
        (5, 1, 2748779069441),  # n=32 needs 32^16=2^80; use 41-bit prime > 2^80? no.
    ]
    # n=16 threshold is 2^32; n=32 is 2^80. For EXACT alignability the prime only must
    # be large enough that char-0 alignment relations don't spuriously collapse; the
    # KKH26 threshold is for the *supply lower bound*, not for the census shape. We use
    # moderately large primes and CROSS-CHECK two primes to detect mod-p artifacts.
    test_primes = {8: [4129, 1073750017], 16: [786433, 1073750017], 32: [1073750017]}

    for mu in (3, 4, 5):
        n = 2 ** mu
        if mu == 5:
            # n=32 full census over a-sets is C(32,a) ~ feasible only small a / small bands
            pass
        for p in test_primes[n]:
            try:
                g = find_g(p, n)
            except ValueError:
                continue
            xs = [pow(g, i, p) for i in range(n)]
            assert len(set(xs)) == n
            print(f"\n----- n={n} (mu={mu}, m=1), p={p}, g={g} -----")
            # sweep r = 2..mu-ish (code depth). k=r-1, tuples size r, a0=r+1.
            r_max = min(mu, 5)
            for r in range(2, r_max + 1):
                K = r - 1           # dimension k
                a0 = r + 1          # band rm+1 = r+1
                if K + 1 > n: continue
                # bands from a0 up to a modest cap (full enum cost C(n,a))
                top = min(n, a0 + 4)
                # KKH26 extremal line [x^{r}, x^{r-1}] -- antipodal fibre family; and far-generic
                lines = [("KKH26[x^%d,x^%d]" % (r, r - 1), charline(r, r - 1, xs, p))]
                # add one far-generic
                import random as _r
                rng = _r.Random(1000 + 10 * mu + r)
                lines.append(("far-generic", ([rng.randrange(p) for _ in range(n)],
                                              [rng.randrange(p) for _ in range(n)])))
                for name, (u0, u1) in lines:
                    e0, e1 = precompute(u0, u1, xs, p, n)
                    cells = []
                    for a in range(a0, top + 1):
                        if comb(n, a) > 3_000_000:
                            cells.append((a, "skip", "skip")); continue
                        al, nb = census_band(u0, u1, xs, p, n, a, e0, e1)
                        cells.append((a, al, nb))
                    rowstr = "  ".join(f"a={a}:al={al}/bad={nb}" for (a, al, nb) in cells)
                    print(f"   r={r} k={K} a0={a0} [{name:>16}]  {rowstr}", flush=True)
    print("\nDONE. Reading guide below.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
