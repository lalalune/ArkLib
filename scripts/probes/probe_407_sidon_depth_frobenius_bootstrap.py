#!/usr/bin/env python3
"""
#407 -- Sidon DEPTH law and FROBENIUS-ORBIT bootstrap for mu_n (B_inf <- B_{log n}).

THE TARGET (issue #407 body, sec.0 / sec.5.0).  mu_n (n=2^a, thin, n <= p^{1/4}) should be a
"B_infinity-Sidon set to depth ell": NO spurious mod-p relation  sum_{i in S} (+-) zeta^i == 0
in F_p  (zeta a primitive n-th root) for a NON-ANTIPODAL subset S with |S| <= ell, BECAUSE the
r-fold root-sums have norm < p for r <= ell.  Provable to depth ell ~ log n.  The OPEN core is
the "B_inf <- B_{log n} bootstrap": extend no-spurious-vanishing from depth log n to ALL depths
(|S| up to n/2).  Equivalently sec.5.0 BIND: no NON-ANTIPODAL subset of mu_n sums to 0 in F_p.

This probe measures the ACTUAL Sidon depth and tests whether the Frobenius-orbit structure of
spurious relations gives a bootstrap, or just multiplies relations.

CONVENTIONS / HONESTY.
- mu_n = the n-th roots of unity in F_p, n=2^a, p == 1 mod n.  zeta = g^{(p-1)/n}, g a generator.
- We work with UNSIGNED zero-sums first (sum_{i in S} zeta^i == 0, S a subset of Z/n indices),
  which is the cleanest sec.5.0 BIND object, then also do the SIGNED (+-) variant.
- "Antipodal pairing": index i and i+n/2 are antipodes (zeta^{i+n/2} = -zeta^i).  An ANTIPODAL
  subset is a union of antipodal pairs {i, i+n/2}; such a set trivially sums to 0 (each pair
  cancels in the SIGNED sense; in the UNSIGNED sense a full antipodal pair {i,i+n/2} sums to
  zeta^i+zeta^{i+n/2}=0).  These are the EXPECTED relations; we exclude them.
- "True regime"/proper subgroup: m=(p-1)/n.  We AVOID high-2-adic-valuation primes (Fermat-like)
  by preferring m ODD (minimal-2-adic prime, m=(p-1)/n odd) where Frobenius order = ord(p mod n).
- Norm prediction: |N_{Q(zeta_n)/Q}(sum_{i in S} zeta^i)|; if < p, the algebraic integer cannot
  vanish mod p, so depth >= |S| for that S.  We take the MIN nonzero norm over r-subsets as the
  norm-floor witness and find the largest r where all r-subsets have |N| < p (norm-predicted depth).

OUTPUTS (no fabrication; everything computed):
  1. measured Sidon depth ell(n,p) vs log2(n) vs norm-predicted depth -> the bootstrap GAP.
  2. Frobenius-orbit analysis of spurious zero-sums: are they orbit-closed? does orbit structure
     bound their count?
  3. verdict on attackability of the bootstrap.
"""

import itertools, sys
from math import gcd, log2

# ---- number theory helpers (pure python, no external deps needed) ----

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    """A generator of F_p^*."""
    if p == 2: return 1
    phi = p - 1
    # factor phi
    facs = set(); m = phi; d = 2
    while d*d <= m:
        while m % d == 0:
            facs.add(d); m //= d
        d += 1
    if m > 1: facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def ord_mod(p, n):
    """multiplicative order of p mod n."""
    o = 1; cur = p % n
    while cur != 1:
        cur = (cur * p) % n; o += 1
    return o

# ---- norm over Q(zeta_n): characteristic-0 floor ----

def norm_of_subset_sum(S, n):
    """
    |N_{Q(zeta_n)/Q}( sum_{i in S} zeta^i )|  computed as the resultant-style product over the
    primitive n-th roots... but for n a 2-power, Gal = (Z/n)^* and N = prod_{k in (Z/n)^*}
    (sum_{i in S} zeta^{k*i}).  We evaluate exactly with python complex then round (n<=64,
    |S|<=n small -> magnitudes are modest; rounding is reliable for these n).  Returns float
    magnitude.  (Used only as a comparative FLOOR indicator, not for the mod-p truth.)
    """
    import cmath
    units = [k for k in range(1, n) if gcd(k, n) == 1]
    prod = 1.0
    for k in units:
        s = sum(cmath.exp(2j*cmath.pi*((k*i) % n)/n) for i in S)
        prod *= abs(s)
    return prod

# ---- the mod-p Sidon depth ----

def zeta_powers(p, n):
    g = primitive_root(p)
    z = pow(g, (p-1)//n, p)          # primitive n-th root
    return [pow(z, i, p) for i in range(n)]  # zeta^0 .. zeta^{n-1}

def is_antipodal_subset(S, n):
    """True iff S is a union of antipodal pairs {i, i+n/2}."""
    h = n//2
    Sset = set(S)
    for i in S:
        if ((i + h) % n) not in Sset:
            return False
    return True

def find_zerosum_subsets(p, n, r, signed=False, limit=None):
    """
    All NON-ANTIPODAL r-subsets S of {0..n-1} with sum_{i in S} (sign) zeta^i == 0 mod p.
    UNSIGNED: plain subset sum.  SIGNED: we range over sign patterns too (eps_i in {+1,-1}),
    reporting (frozenset, signtuple).  Returns list (capped by `limit`).
    """
    zp = zeta_powers(p, n)
    out = []
    for S in itertools.combinations(range(n), r):
        if is_antipodal_subset(S, n):
            continue
        if not signed:
            if sum(zp[i] for i in S) % p == 0:
                out.append(frozenset(S))
                if limit and len(out) >= limit:
                    return out
        else:
            # iterate sign patterns; skip the all-(+) duplicate handling by canonicalizing
            found_here = False
            for signs in itertools.product((1, -1), repeat=r):
                if signs[0] != 1:   # canonical: first sign +
                    continue
                acc = 0
                for idx, i in enumerate(S):
                    acc += signs[idx]*zp[i]
                if acc % p == 0:
                    out.append((frozenset(S), signs))
                    found_here = True
            if limit and len(out) >= limit:
                return out
    return out

def measured_sidon_depth(p, n, signed=False, rmax=None):
    """max r such that NO non-antipodal r-subset (UNSIGNED) sums to 0; scan r=1.. until a hit."""
    if rmax is None:
        rmax = n//2
    for r in range(1, rmax+1):
        hits = find_zerosum_subsets(p, n, r, signed=signed, limit=1)
        if hits:
            return r - 1, r, hits[0]   # depth = r-1, first failing r, a witness
    return rmax, None, None

def norm_predicted_depth(n, p, rmax=None):
    """largest r such that EVERY non-antipodal r-subset has |N| < p (so cannot vanish mod p)."""
    if rmax is None:
        rmax = n//2
    depth = 0
    for r in range(1, rmax+1):
        all_below = True
        any_subset = False
        for S in itertools.combinations(range(n), r):
            if is_antipodal_subset(S, n):
                continue
            any_subset = True
            nm = norm_of_subset_sum(S, n)
            # nm could be ~0 (char-0 vanishing => Lam-Leung relation); treat <1e-6 as 0 (vanishes,
            # so it would vanish mod every p -> norm prediction fails for that S)
            if nm < 1e-6 or nm >= p:
                all_below = False
                break
        if not any_subset:
            break
        if all_below:
            depth = r
        else:
            break
    return depth

# ---- Frobenius orbit machinery ----

def frobenius_orbit_unsigned(S, n, p):
    """
    Orbit of subset S (set of indices in Z/n) under index map i -> p*i mod n (Frobenius).
    If sum zeta^i == 0 then sum zeta^{p i} == 0 (apply x->x^p, char p).  Returns the orbit set
    of frozensets.
    """
    orbit = set()
    cur = frozenset(S)
    while cur not in orbit:
        orbit.add(cur)
        cur = frozenset((p*i) % n for i in cur)
    return orbit

def dilation_orbit_unsigned(S, n):
    """
    Orbit under DILATION i -> i+t mod n (mult-by-zeta^t; mu_n is dilation invariant, so a zero-sum
    stays a zero-sum: sum zeta^{i+t} = zeta^t sum zeta^i = 0).  Cyclic group of size n.
    """
    orbit = set()
    for t in range(n):
        orbit.add(frozenset((i+t) % n for i in S))
    return orbit

# ============================ MAIN ============================

def pick_primes(n, want=4, prefer_odd_m=True, pmax=200000):
    """primes p == 1 mod n; prefer m=(p-1)/n ODD (minimal 2-adic, true regime)."""
    odd, evn = [], []
    p = n+1
    while len(odd) < want and p < pmax:
        if is_prime(p):
            m = (p-1)//n
            (odd if m % 2 == 1 else evn).append((p, m, ord_mod(p, n)))
        p += n
    return odd, evn

def section1_depth_law():
    print("="*78)
    print("SECTION 1 -- Sidon depth law  ell(n,p)  vs  log2(n)  vs  norm-predicted depth")
    print("="*78)
    print("(UNSIGNED zero-sums = sec.5.0 BIND object; antipodal subsets excluded)")
    print(f"{'n':>4} {'a':>3} {'p':>9} {'m=(p-1)/n':>10} {'m_odd':>6} {'ord(p,n)':>9} "
          f"{'meas_depth':>11} {'1st_fail_r':>11} {'log2 n':>7} {'norm_pred':>10}")
    summary = []
    for a in (4, 5, 6):
        n = 2**a
        odd, evn = pick_primes(n, want=3)
        # combine but mark; prefer odd-m (true regime), include one even-m for contrast
        rows = [(p,m,o,True) for (p,m,o) in odd] + [(p,m,o,False) for (p,m,o) in evn[:1]]
        for (p, m, o, is_odd) in rows:
            rmax = n//2
            depth, fail_r, wit = measured_sidon_depth(p, n, signed=False, rmax=rmax)
            npd = norm_predicted_depth(n, p, rmax=rmax)
            print(f"{n:>4} {a:>3} {p:>9} {m:>10} {str(m%2==1):>6} {o:>9} "
                  f"{depth:>11} {str(fail_r):>11} {log2(n):>7.2f} {npd:>10}")
            summary.append((n, p, m%2==1, depth, fail_r, npd))
    print()
    print("READING: bootstrap gap = (n/2) - meas_depth  [how far PAST log n the property holds].")
    for (n,p,modd,depth,fail_r,npd) in summary:
        nmax = n//2
        gap = nmax - depth
        status = "HOLDS to n/2 (no spurious)" if fail_r is None else f"FAILS at r={fail_r}"
        print(f"  n={n:>3} p={p:>8} m_odd={str(modd):>5}: meas_depth={depth:>2} "
              f"(log2 n={log2(n):.1f}, norm_pred={npd}, n/2={nmax})  -> {status}")
    return summary

def section2_frobenius():
    print()
    print("="*78)
    print("SECTION 2 -- Frobenius-orbit structure of spurious zero-sums")
    print("="*78)
    print("Look for n,p where spurious (non-antipodal) zero-sums EXIST, then analyze orbits.")
    found_any = False
    # search a wider band, including even-m (Fermat-ish) primes where spurious relations appear
    for a in (4, 5):
        n = 2**a
        p = n+1
        examined = 0
        while examined < 60 and p < 500000:
            if is_prime(p):
                examined += 1
                # scan small-to-mid r for any spurious zero-sum
                hit = None
                for r in range(2, n//2+1):
                    hs = find_zerosum_subsets(p, n, r, signed=False, limit=1)
                    if hs:
                        hit = (r, hs[0]); break
                if hit is not None:
                    r, S = hit
                    found_any = True
                    m = (p-1)//n
                    forb = frobenius_orbit_unsigned(S, n, p)
                    dorb = dilation_orbit_unsigned(S, n)
                    ordpn = ord_mod(p, n)
                    # verify ALL frobenius images are also zero-sums (the claimed structure)
                    zp = zeta_powers(p, n)
                    all_zero = all(sum(zp[i] for i in T) % p == 0 for T in forb)
                    all_zero_dil = all(sum(zp[i] for i in T) % p == 0 for T in dorb)
                    print(f"\n  n={n} p={p} (m={m}, m_odd={m%2==1}, ord(p mod n)={ordpn})")
                    print(f"    smallest spurious zero-sum: r={r}  S={sorted(S)}")
                    print(f"    Frobenius orbit (i->p*i mod n) size = {len(forb)}  "
                          f"(ord(p,n)={ordpn})  all-zero-sum? {all_zero}")
                    print(f"    Dilation orbit (i->i+t mod n)  size = {len(dorb)}  "
                          f"all-zero-sum? {all_zero_dil}")
                    # count ALL spurious zero-sums at this r and group into orbits
                    allhits = find_zerosum_subsets(p, n, r, signed=False)
                    allset = set(allhits)
                    # partition by combined dilation+frobenius closure
                    seen = set(); orbits = []
                    for T in allset:
                        if T in seen: continue
                        # full orbit under the group generated by frobenius and dilation
                        comp = set([T]); frontier = [T]
                        while frontier:
                            U = frontier.pop()
                            imgs = [frozenset((p*i)%n for i in U)] + \
                                   [frozenset((i+t)%n for i in U) for t in range(1,n)]
                            for V in imgs:
                                if V in allset and V not in comp:
                                    comp.add(V); frontier.append(V)
                        orbits.append(comp); seen |= comp
                    print(f"    TOTAL spurious r={r} zero-sums = {len(allset)}; "
                          f"# (dilation+Frobenius)-orbits = {len(orbits)}; "
                          f"orbit sizes = {sorted(len(o) for o in orbits)}")
                    break  # one example per (n) is enough for the structure read
            p += n
        if not found_any and a == 5:
            print(f"  (n={n}: no spurious zero-sum found in band scanned)")
    if not found_any:
        print("  No spurious non-antipodal zero-sums found in scanned bands at any n.")
    return found_any

def section3_largen_dyadic_norm():
    print()
    print("="*78)
    print("SECTION 3 -- norm-floor depth law (char-0): how far does |N|<p reach as p grows?")
    print("="*78)
    print("For fixed n, increase p; norm-predicted depth should track where the LARGEST r-subset")
    print("norm crosses p.  This isolates the GENUINE bootstrap gap (norm-floor vs full n/2).")
    print(f"{'n':>4} {'p':>10} {'p^(1/4)':>9} {'n<=p^.25?':>10} {'norm_pred_depth':>15} "
          f"{'log2 n':>7} {'max|N|@r=2':>12}")
    for a in (4, 5, 6):
        n = 2**a
        # pick a prize-scale-ish prime where n <= p^{1/4}, i.e. p >= n^4
        target = n**4
        p = target + (n - (target % n)) % n + 1
        while not (is_prime(p) and p % n == 1):
            p += n
        npd = norm_predicted_depth(n, p, rmax=min(n//2, 8))  # cap rmax for runtime at large n
        # report the max norm among r=2 subsets for scale
        max2 = 0.0
        for S in itertools.combinations(range(n), 2):
            if is_antipodal_subset(S, n): continue
            max2 = max(max2, norm_of_subset_sum(S, n))
        print(f"{n:>4} {p:>10} {p**0.25:>9.1f} {str(n <= p**0.25):>10} {npd:>15} "
              f"{log2(n):>7.2f} {max2:>12.2e}  (rmax capped at {min(n//2,8)})")
    print("\nNOTE: norm-predicted depth here is a LOWER bound on true depth (it only certifies")
    print("non-vanishing for r where ALL subset norms < p; larger r may still be safe mod the")
    print("specific p).  The measured depth in Section 1 is the GROUND TRUTH.")

if __name__ == "__main__":
    s1 = section1_depth_law()
    found = section2_frobenius()
    section3_largen_dyadic_norm()
    print()
    print("="*78)
    print("DONE.  See structured verdict in the accompanying finding.")
    print("="*78)


# ============================================================================
# SECTION 4 (appended) -- THE THIN REGIME (n <= p^{1/4}, p >= n^4): the actual
# prize regime.  Section 1 used tiny primes (p ~ n..16n) where mu_n is DENSE in
# F_p and spurious relations are forced by pigeonhole -- NOT the prize regime.
# Here p >= n^4 so mu_n is genuinely thin.  We measure true UNSIGNED Sidon depth
# (full r, no rmax cap, with a hit-search that short-circuits) for a=4,5 and a
# couple thin primes each, plus the SIGNED depth at small r.
# ============================================================================

# NOTE on the THIN regime (the actual prize regime, p >= n^4, n <= p^{1/4}):
# Section 1 above uses tiny primes (p ~ n..16n) where mu_n is DENSE in F_p, so spurious
# zero-sums are forced by pigeonhole and the measured depth is artificially small -- NOT the
# prize regime.  Measuring the true Sidon depth in the thin regime needs a meet-in-the-middle
# subset-sum search (the naive O(C(n,r)) scan is infeasible at n=32: C(32,16)~6e8).  That is
# done in the companion probe `probe_407_sidon_thin_regime_mitm.py`, with the orbit-count
# analysis in `probe_407_frobenius_count_constraint.py`.  Summary of those results:
#   n=16, p>=65537 (thin): NO non-antipodal zero-sum below n/2 -- BIND HOLDS OUTRIGHT (15/15 primes).
#   n=32, p~1e6   (thin): smallest non-antipodal zero-sum at r~10-11 (> log2(32)=5, < n/2=16);
#                          BIND is literally FALSE; the count at the binding band is an exact
#                          multiple of n (pure dilation orbits), O(n) up to ~r0+3.
#   Frobenius is TRIVIAL in the admissible regime (p=1 mod n => i->p*i=i), so the only symmetry
#   is dilation; the bootstrap reduces to bounding the # of dilation-orbits = the BGK count wall.
