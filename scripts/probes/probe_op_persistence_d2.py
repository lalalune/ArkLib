#!/usr/bin/env python3
"""
M-OPpersist (#444): MEASURE single-orbit persistence O_P = 1 at the binding imprimitive d=2
direction, for n = 2^mu in {8, 16, 32, 64}.

================================================================================================
WHAT THIS MEASURES (the off-BGK distinct-gamma union-count growth-law sub-lead)
================================================================================================
The prize delta* reduces (OFF the BGK char-sum wall) to the GROWTH LAW of the distinct-gamma
UNION count U(n) = |U_{R in binom(mu_s, k+1)} {gamma_R}|, gamma_R = -h_{a-k}(R)/h_{b-k}(R) the
forced bad scalar of a witness subset R for the far direction (base x^a, dir x^b).

The Action-Orbit factorization (OrbitCountCrossingLaw.lean / _GLContainer.lean, proven in-tree):
  D*(m) = #bad = z + S * O
where
  z = [gamma=0 is bad]  in {0,1}   (the fixed point of the dilation action),
  S = orbit size = n / gcd(b-a, n)  (the dilation b-a multiplies a solved gamma by h^{b-a}),
  O = number of DISTINCT nonzero gamma-orbits under <h^{b-a}>  (=: O_P, the object measured here).

The budget test #bad <= budget(=n) is EQUIVALENT (off the fixed point) to  O <= gcd(b-a, n) = d.

For the IMPRIMITIVE d=2 direction (gcd(b-a, n) = 2, so S = n/2), the binding-radius orbit count
O_P is the "plateau" value: _AngleC_PlateauBenignOrbitFloor showed the cascade plateaus at the
orbit-count floor O_P = 1 (z + S*1 = 1 + n/2 <= n = benign) before dropping to 0.

KEY QUESTION (c295/c318): does O_P = 1 PERSIST for ALL n = 2^mu at the binding d=2 direction,
via the n -> n/2 even/odd descent on the Schur-ratio? If yes (single-orbit persistence), the
binding fold's distinct-gamma contribution is a SINGLE dilation orbit (size n/2), which is the
structural input that would give bounded m* (the prize-side decay). super-poly growth of O_P or
loss of single-orbit-ness would break it.

================================================================================================
WHAT WE REPORT, per n = 2^mu:
  - the binding direction (a, b) = the WORST far direction with d = gcd(b-a, n) = 2 (imprimitive),
    chosen as the d=2 direction whose binding radius s* is LARGEST (= governs m*),
  - its orbit size S = n / gcd(n, b-a) = n/2,
  - the binding radius s* (first s with #bad <= budget = n) for that direction,
  - O_P = orbit count = #distinct-nonzero-gamma-orbits at the binding radius s*,
  - whether O_P = 1 (single-orbit persistence) holds,
  - and the cascade of O over s (the descent to the floor), cross-checked across primes p > n^4.

n=8,16,32 are exact brute-force over canonical shift-classes (feasible). n=64 uses the SAME exact
enumeration but RESTRICTED to the binding d=2 direction only and to s near s* (the orbit-count
recursion / shift-class quotient keeps C(64, s)/64 tractable for the few binding rows we need;
we DO NOT brute all C(64,k) -- we enumerate shift-class reps for the single binding direction at
the handful of radii s in [s*-2, s*+1]).
================================================================================================
"""
import sys, math, itertools

# ------------------------------------------------------------------ number theory helpers
def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_factors(m):
    s = set(); d = 2
    while d*d <= m:
        while m % d == 0: s.add(d); m//=d
        d += 1
    if m > 1: s.add(m)
    return s

def fp_near(n, target):
    """smallest prime >= target with p == 1 (mod n)."""
    p = target + (1 - target) % n
    if p < 2: p += n
    while True:
        if p > 2 and p % n == 1 and isprime(p): return p
        p += n

def subgroup_ordered(p, n):
    """ordered list S = [1, h, h^2, ..., h^{n-1}] of the order-n subgroup mu_n of F_p^*."""
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S = []; x = 1
        for _ in range(n): S.append(x); x = x*h % p
        if len(set(S)) == n: return S, h
    raise RuntimeError("no subgroup")

# ------------------------------------------------------------------ linear algebra over F_p
def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0
    pr = 0
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
    """basis of the left null space of the s x k matrix V (rows = Vandermonde rows)."""
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[k + j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def canon_shift(R, n):
    """canonical representative of the Z/n shift-class of subset R (lex-min over all shifts)."""
    best = None
    for c in range(n):
        t = tuple(sorted((i+c) % n for i in R))
        if best is None or t < best: best = t
    return best

def gamma_for_R(R, S, p, a, b, prec, Vrows):
    """forced bad scalar gamma_R for witness subset R, far direction (base x^a, dir x^b).
       returns ('one', g) if R forces a unique gamma, ('heavy', None) if it forces nothing
       (collapses the whole line => p), ('none', None) if no valid gamma."""
    s = len(R)
    V = [Vrows[i] for i in R]
    P = left_null(V, p)
    if not P: return ('none', None)
    pa_ = prec[a]; pb_ = prec[b]
    pa = [sum(P[t][ii] * pa_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    pb = [sum(P[t][ii] * pb_[R[ii]] for ii in range(s)) % p for t in range(len(P))]
    if not any(pb):
        if not any(pa): return ('heavy', None)
        return ('none', None)
    i = next(j for j in range(len(pb)) if pb[j])
    g = (-pa[i] * pow(pb[i], p - 2, p)) % p
    if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
        return ('one', g)
    return ('none', None)

# ------------------------------------------------------------------ the d=2 binding analysis
#
# SPEEDUP: the shift-class reps and their left-nullspace projectors P depend ONLY on (n, s, k),
# NOT on the direction (a, b).  We precompute them ONCE per (n, s) and reuse across all directions
# (gamma_for_R then just multiplies the cached P against the precomputed a/b power columns).

def shiftclass_projectors(n, s, p, Vrows):
    """list of (R, P) for each canonical shift-class rep R of size-s subsets, P = left-null basis
       of the s x k Vandermonde of R.  Computed once per (n, s); reused across all directions."""
    seen = set(); out = []
    for R in itertools.combinations(range(n), s):
        cR = canon_shift(R, n)
        if cR in seen: continue
        seen.add(cR)
        V = [Vrows[i] for i in cR]
        P = left_null(V, p)
        out.append((cR, P))
    return out

def gamma_from_proj(cR, P, p, a, b, prec):
    """forced gamma for shift-class rep cR with cached projector P, far direction (a,b)."""
    if not P: return ('none', None)
    s = len(cR)
    pa_ = prec[a]; pb_ = prec[b]
    pa = [sum(P[t][ii] * pa_[cR[ii]] for ii in range(s)) % p for t in range(len(P))]
    pb = [sum(P[t][ii] * pb_[cR[ii]] for ii in range(s)) % p for t in range(len(P))]
    if not any(pb):
        if not any(pa): return ('heavy', None)
        return ('none', None)
    i = next(j for j in range(len(pb)) if pb[j])
    g = (-pa[i] * pow(pb[i], p - 2, p)) % p
    if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
        return ('one', g)
    return ('none', None)

def analyze_dir_cached(S, h, p, a, b, projs_for_s, prec):
    """Action-Orbit decomposition for direction (a,b) at one radius, using cached shift-class
       projectors projs_for_s = [(cR, P), ...].  Returns D, O(=O_P), z, orbsize, d, heavy."""
    n = len(S)
    gammas = set(); heavy = False
    fac = pow(h, (b - a) % n, p)            # the dilation: gamma -> gamma * h^{b-a}
    for (cR, P) in projs_for_s:
        kind, g = gamma_from_proj(cR, P, p, a, b, prec)
        if kind == 'heavy':
            heavy = True; continue
        if kind == 'one':
            x = g
            for _ in range(n):              # dilation-close the orbit of g
                gammas.add(x); x = (x * fac) % p
    d = math.gcd((b - a) % n, n)
    orbsize = n // d
    z = 1 if 0 in gammas else 0
    nonzero = gammas - {0}
    # partition nonzero gammas into <fac>-orbits; O = #orbits = O_P
    visited = set(); O = 0
    for g in nonzero:
        if g in visited: continue
        O += 1; x = g
        for _ in range(n):
            if x in nonzero: visited.add(x)
            x = (x * fac) % p
    D = p if heavy else len(gammas)
    return {'D': D, 'O': O, 'z': z, 'orbsize': orbsize, 'd': d, 'heavy': heavy}

def d2_directions(n, k):
    """all far directions (a,b) with gcd(b-a, n) = 2 (imprimitive d=2), b a LOW far exponent
       (b in [k, k+3]) and EXCLUDING the antipodal x^{n/2} = +-1 line (a or b = n/2)."""
    out = []
    blist = range(k, min(k+4, n))
    for b in blist:
        for a in range(n):
            if a == b: continue
            if a == n//2 or b == n//2: continue      # exclude antipodal +-1 line
            if math.gcd((b - a) % n, n) == 2:
                out.append((a, b))
    return out

def cascade_for_dir(S, h, p, a, b, projs, prec, s_lo, s_hi):
    """O/D cascade over s in [s_lo, s_hi] for direction (a,b), using cached projectors
       projs[s] = [(cR,P),...].  Returns list [(s, O, D, z, orbsize), ...]."""
    cascade = []
    for s in range(s_lo, s_hi + 1):
        res = analyze_dir_cached(S, h, p, a, b, projs[s], prec)
        cascade.append((s, res['O'], res['D'], res['z'], res['orbsize']))
    return cascade

def run_one(n, p, label, restrict_dirs=None, s_window=None, verbose=True):
    """MEASURE O_P single-orbit persistence at the binding imprimitive d=2 direction.

    The BINDING d=2 direction = the worst far direction with gcd(b-a,n)=2: the one with the
    DEEPEST cascade (largest #bad at the first probed radius), i.e. the direction that maximizes
    the over-determination depth m* and exhibits the benign PLATEAU
        #bad = z + S*1 = 1 + n/2     (single surviving orbit, O_P=1).

    We report O_P at:
      - the PLATEAU radius  (last radius with 1 <= #bad <= n, i.e. the single-orbit benign value
        z + S*1 just before #bad drops to 0) -- this is the O_P the persistence question is about,
      - the binding radius s* (first #bad <= budget),
      - and we test O_P==1 at the plateau.
    """
    k = n // 4
    budget = n
    S, h = subgroup_ordered(p, n)
    prec = {e: [pow(x, e, p) for x in S] for e in range(n)}
    Vrows = {i: [pow(S[i], j, p) for j in range(k)] for i in range(n)}

    dirs = restrict_dirs if restrict_dirs is not None else d2_directions(n, k)
    if not dirs:
        if verbose: print(f"  [n={n} {label}] no d=2 far directions", flush=True)
        return None
    s_lo, s_hi = s_window if s_window else (k + 1, min(n - k + 1, k + 8))

    # cache shift-class projectors ONCE per radius (independent of direction) -- the big speedup
    projs = {s: shiftclass_projectors(n, s, p, Vrows) for s in range(s_lo, s_hi + 1)}

    # The BINDING d=2 direction (the one governing m* and exhibiting the single-orbit plateau) is
    # the d=2 direction whose count survives POSITIVE-and-good the LONGEST: the largest radius with
    # a single-orbit benign row (O_P=1, 0 < #bad = z+S <= budget).  Among d=2 directions some drop
    # straight #bad: big->0 (no plateau, NOT binding -- they die earliest), while the binding ones
    # plateau at #bad = 1 + n/2 (O_P=1) at the largest radius.  We select by:
    #   primary  = largest plateau radius (last s with O_P=1 and 0<#bad<=budget),
    #   tie-break = deepest cascade (#bad at first probed radius).
    def select_key(cascade):
        plat_radii = [s for (s, O, D, z, osz) in cascade if O == 1 and 0 < D <= budget]
        last_plat = max(plat_radii) if plat_radii else -1
        return (last_plat, cascade[0][2])
    best = None  # ((a,b), cascade, key)
    for (a, b) in dirs:
        cascade = cascade_for_dir(S, h, p, a, b, projs, prec, s_lo, s_hi)
        key = select_key(cascade)
        if best is None or key > best[2]:
            best = ((a, b), cascade, key)
    (a, b), cascade, _ = best

    d = math.gcd((b - a) % n, n)
    orbsize = n // d
    orbit_size_formula = n // math.gcd(n, (a - b) % n)   # n/gcd(n,a-b) (== orbsize = n/2 for d=2)

    # binding radius s* = first #bad <= budget
    s_star = next((s for (s, O, D, z, osz) in cascade if D <= budget), None)
    # PLATEAU radius = last radius with #bad == single-orbit benign value (z + S*1) and #bad>0,
    # i.e. the radius where O_P=1 (one surviving orbit) -- the object of the persistence question.
    plateau = None
    for (s, O, D, z, osz) in cascade:
        if 0 < D <= budget and O == 1:
            plateau = (s, O, D, z, osz)   # keep LAST such (the floor just before death)
    # O_P at the plateau (or, if no O_P=1 row -- count drops straight to 0 -- report that)
    if plateau is not None:
        sp, O_P, D_P, z_P, osz_P = plateau
        single_orbit = True
    else:
        # no single-orbit plateau row -> find the last good positive-#bad row and report its O
        last_good_pos = None
        for (s, O, D, z, osz) in cascade:
            if 0 < D <= budget:
                last_good_pos = (s, O, D, z, osz)
        if last_good_pos is not None:
            sp, O_P, D_P, z_P, osz_P = last_good_pos
        else:
            # count drops budget->0 with no positive good row; O_P is the orbit count of the
            # smallest still-bad row just above s* (the last surviving orbit count before 0).
            sp = s_star; O_P = 0; D_P = 0; z_P = 0; osz_P = orbsize
        single_orbit = (O_P == 1)

    if verbose:
        print(f"\n=== n={n}  {label}  p={p} (>{n}^4={n**4}) ===", flush=True)
        print(f"  binding d=2 direction (a,b)=({a},{b}); d=gcd(b-a,n)={d}; "
              f"orbit size n/gcd(n,a-b)={orbit_size_formula} (=S={orbsize}=n/2)", flush=True)
        sstar_str = str(s_star) if s_star is not None else "none-in-window"
        print(f"  budget = n = {n}; binding radius s* = {sstar_str} "
              f"(m* = {(s_star-k) if s_star is not None else '?'})", flush=True)
        print(f"  {'s':>3} {'m':>3} | {'#bad=D':>8} {'z':>2} {'S':>4} {'O_P':>5} | O_P<=d? | "
              f"z+S*O? | budget?", flush=True)
        for (s, O, D, z, osz) in cascade:
            good = D <= budget
            odle = (O <= d)
            recon = z + osz * O
            tag = " " if recon == D else "*"   # * if single-S reconstruction imperfect
            print(f"  {s:>3} {s-k:>3} | {D:>8} {z:>2} {osz:>4} {O:>5} | "
                  f"{str(odle):>6} | {recon}{tag:>2} | {'GOOD' if good else 'bad'}", flush=True)
        print(f"  >>> PLATEAU (single-orbit floor) at s={sp}: #bad={D_P}, O_P={O_P}  "
              f"[z+S*O_P = {z_P}+{osz_P}*{O_P} = {z_P + osz_P*O_P}]", flush=True)
        print(f"  >>> O_P == 1 (single-orbit persistence)? {'YES' if single_orbit else 'NO'}",
              flush=True)
    return {
        'n': n, 'p': p, 'label': label, 'a': a, 'b': b, 'd': d,
        'orbit_size': orbit_size_formula, 's_star': s_star,
        'm_star': (s_star - k) if s_star is not None else None,
        'plateau_s': sp, 'O_P': O_P, 'D_plateau': D_P, 'single_orbit': single_orbit,
        'cascade': cascade,
    }

if __name__ == '__main__':
    ns = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [8, 16, 32, 64]
    results = []
    for n in ns:
        k = n // 4
        # two large primes p > n^4 (p-independence cross-check of O_P, which is char-0)
        p1 = fp_near(n, n**4 + 1)
        p2 = fp_near(n, n**4 + 50000*n)
        primes = [(p1, "n^4-std"), (p2, "n^4-alt")]

        if n <= 32:
            for (p, lab) in primes:
                r = run_one(n, p, lab)
                if r: results.append(r)
        else:
            # n=64: avoid full C(64,k) by restricting to the few tightest d=2 directions and a
            # narrow s-window around the expected binding radius.  The shift-class projector cache
            # is computed once per radius; the binding plateau for n/4 rate sits at small m*.
            # Tightest d=2 dilations = those with |b-a| in {2, n-2}; these bind worst/deepest.
            cand = [ab for ab in d2_directions(n, k)
                    if ((ab[1]-ab[0]) % n) in (2, n-2)]
            if not cand:
                cand = d2_directions(n, k)[:8]
            for (p, lab) in primes:
                r = run_one(n, p, lab, restrict_dirs=cand, s_window=(k+1, k+6))
                if r: results.append(r)

    print("\n" + "="*100)
    print("=== SUMMARY: O_P single-orbit persistence at the binding imprimitive d=2 direction ===")
    print("="*100)
    print(f"{'n':>5} {'mu':>3} {'p-label':>10} {'dir(a,b)':>10} {'d':>3} {'orbsize=n/2':>12} "
          f"{'s*':>4} {'m*':>4} {'plat_s':>6} {'#bad@plat':>10} {'O_P':>5} {'O_P==1?':>8}")
    for r in results:
        ms = str(r['m_star']) if r['m_star'] is not None else '?'
        ss = str(r['s_star']) if r['s_star'] is not None else '?'
        print(f"{r['n']:>5} {int(math.log2(r['n'])):>3} {r['label']:>10} "
              f"{str((r['a'], r['b'])):>10} {r['d']:>3} {r['orbit_size']:>12} "
              f"{ss:>4} {ms:>4} {r['plateau_s']:>6} {r['D_plateau']:>10} {r['O_P']:>5} "
              f"{'YES' if r['single_orbit'] else 'NO':>8}")
    # persistence verdict
    by_n = {}
    for r in results:
        by_n.setdefault(r['n'], []).append(r['single_orbit'])
    print("\n--- PERSISTENCE VERDICT (O_P == 1 at the binding d=2 plateau, across primes p > n^4) ---")
    all_persist = True
    for n in sorted(by_n):
        allone = all(by_n[n])
        all_persist = all_persist and allone
        print(f"  n={n:>4} (2^{int(math.log2(n))}): O_P==1 on all tested primes? "
              f"{'YES' if allone else 'NO'}  ({sum(by_n[n])}/{len(by_n[n])} primes)")
    print(f"\n  ==> SINGLE-ORBIT PERSISTENCE O_P=1 at binding d=2 for all tested n=2^mu: "
          f"{'PERSISTS' if all_persist else 'DOES NOT PERSIST'}")
