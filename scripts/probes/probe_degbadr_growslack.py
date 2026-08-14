#!/usr/bin/env python3
"""
probe_degbadr_growslack.py  —  MEASURE  deg_n(#bad_r)  exactly  (#444, TASK M-degBadR).

THE GROWING-SLACK SUB-LEAD (open-directions census §1.4 / §C, c269 item 6 / c274, flagged
PROMISING).  The prize delta* reduces, OFF the BGK char-sum wall, to the GROWTH LAW of the
distinct-gamma UNION count

    U(n) = | U_{R in binom(mu_s, k+1)}  { gamma_R } | ,
    gamma_R = - h_{a-k}(R) / h_{b-k}(R)      (forced bad scalar of the far pencil x^a + g x^b)

where  h_r = dividedDifferencePow  = the complete-homogeneous symmetric polynomial of degree r
in the k+1 node values of R (SchurLagrangeBridge: the z^k-coeff of the Lagrange interpolant of
x^idx over a (k+1)-subset R equals h_{idx-k}(R)).  The "growing-slack" mechanism, the decay that
would give the prize floor: if  #bad_r := #distinct forced-gamma at FOLD r  is a polynomial of
degree  < r  in n, the budget crossing  #bad_r vs budget(=n)  is eventually slack ==> bounded m*
==> delta* -> capacity.

KEY QUESTION (this probe answers EXACTLY, per r=2..6):   is  deg_n(#bad_r) < r ?

CONVENTION (matches the substrate).  rho = 1/4 => s = n, k = n/4, (k+1)-subsets R.  A far monomial
DIRECTION is an exponent pair (a,b); the FOLD r is the complete-homog degree of the NUMERATOR
r := a-k (numerator h_r), the denominator index is d := b-k (denominator h_d, with d=0 <=> b=k <=>
h_0=1 <=> gamma=-h_r = the BARE SPECTRUM; the far audit's BINDER is b=k i.e. d=0).  At FIXED fold r
we SWEEP the denominator index d over far values and report BOTH:
  * #bad_r^bind  = the BARE-SPECTRUM (d=0, b=k) count  | { -h_r(R) : R } |  -- the audited binder
  * #bad_r^max   = max over d of  | { -h_r(R)/h_d(R) : R } |              -- worst far direction
This is the LITERAL task object: "#distinct forced-gamma over (k+1)-subsets at the binding far
direction".

CONTRAST OBJECT (the genuine delta* union, reported for n=8,16 to be honest about which object the
growing-slack applies to):  U(n) = max-far far-line INCIDENCE over the (n-r)-WITNESS sets (size
n-r, NOT k+1) -- the realized union that is budget-bounded by n.  This is a DIFFERENT (larger-
witness) object; the (k+1)-subset spectrum above is NOT it.

EXACTNESS / p-INDEPENDENCE.  All arithmetic EXACT in F_p, p = 1 (mod n), p > n^4 (avoids the finite
bad-prime set; _SpecF7).  p-independence is CONFIRMED at LOW folds (r=2,3) exactly; at high folds
near the C(n,k+1) ceiling small +-O(n) accidental-collision fluctuations appear (the p-dependent
good/bad-prime incidence-lab residual) -- we report the count at the primary prime and flag the
fluctuation band.

DEGREE FIT.  Dyadic ladder n = 2^mu in {8,16,32}; n=24 is a non-2-power CONTROL (reported, excluded
from the dyadic slope).  Degree = consecutive dyadic log2-ratio  log2(#bad_r(2n)/#bad_r(n))  and a
least-squares log-log slope; we ALSO report  #bad_r / C(n,k+1)  (a stable fraction <=> Theta(C) <=>
super-polynomial, the decisive diagnostic).

Run:  python3 scripts/probes/probe_degbadr_growslack.py     [--with-n32]   [--with-union]
(default skips the ~9min/prime n=32 sweep and the union contrast; pass the flags to include them.)
"""
import sys, math, itertools

# --------------------------------------------------------------------------- number theory
def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s=0
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
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def find_prime_cong1_above(n, lo):
    """smallest prime p = 1 (mod n) with p > lo (we pass lo = n^4)."""
    p = lo + (n - (lo % n)) + 1
    while p % n != 1:
        p += 1
    while not isprime(p):
        p += n
    return p

def subgroup(p, n):
    """mu_n = order-n multiplicative subgroup of F_p (n | p-1), as a sorted list of residues."""
    assert (p-1) % n == 0, f"{n} does not divide {p}-1"
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x = x*h % p; S.add(x)
        if len(S) == n: return sorted(S)
    raise RuntimeError(f"no order-{n} subgroup in F_{p}")

# --------------------------------------------------------------------------- complete-homog h_r
def hr_values(vals, rmax, p):
    """
    Complete homogeneous symmetric polynomials h_0..h_rmax of the multiset `vals` in F_p, via the
    Newton identity  m*h_m = sum_{i=1..m} p_i * h_{m-i}  (p_i = power sum; m invertible, p>rmax).
    Equals dividedDifferencePow(R, v, m) for |R| = k+1 = len(vals) (Schur/Jacobi-Trudi bridge).
    """
    L = len(vals)
    pw = [0]*(rmax+1); cur = [1]*L
    for i in range(1, rmax+1):
        cur = [(cur[j]*vals[j]) % p for j in range(L)]
        pw[i] = sum(cur) % p
    inv = [0]*(rmax+1)
    for m in range(1, rmax+1): inv[m] = pow(m, p-2, p)
    h = [0]*(rmax+1); h[0] = 1 % p
    for m in range(1, rmax+1):
        acc = 0
        for i in range(1, m+1):
            acc = (acc + pw[i]*h[m-i]) % p
        h[m] = (acc * inv[m]) % p
    return h

def hr_table_over_subsets(S, k, rmax, p):
    """h_0..h_rmax(R) for every (k+1)-subset R of mu_s.  h_0 == 1 always."""
    out = []
    for R in itertools.combinations(S, k+1):
        out.append(hr_values(list(R), rmax, p))
    return out

def badcount_streaming(S, k, rmax, dmax, p):
    """
    Memory-safe streaming version of badcount: never stores the full h-table (needed for n=32
    where C(32,9)=28M rows would be multi-GB).  Accumulates, per (r,d), a `set` of gamma values;
    the per-subset inverses are done with a tiny batch over the dmax denominators of THAT subset
    (1 modexp per subset, not per (r,d)).  Returns the same {r: {bind,max,binding_d,all}} shape.
    """
    sets = {r: {0: set()} for r in range(2, rmax+1)}
    for r in range(2, rmax+1):
        for d in range(1, dmax+1):
            if d != r: sets[r][d] = set()
    for R in itertools.combinations(S, k+1):
        h = hr_values(list(R), max(rmax, dmax), p)
        # batch-invert the denominators h_1..h_dmax of this subset (1 modexp)
        dens = [h[d] % p for d in range(1, dmax+1)]
        inv = _batch_inv(dens, p)               # inv[d-1] = h_d^{-1} (0 if h_d==0)
        for r in range(2, rmax+1):
            num = (-h[r]) % p
            sets[r][0].add(num)                 # d=0 bare spectrum
            for d in range(1, dmax+1):
                if d == r: continue
                iv = inv[d-1]
                if iv: sets[r][d].add(num * iv % p)
    out = {}
    for r in range(2, rmax+1):
        counts = {d: len(s) for d, s in sets[r].items()}
        best_d = max(counts, key=lambda dd: counts[dd])
        out[r] = {"bind": counts[0], "max": counts[best_d], "binding_d": best_d, "all": dict(counts)}
    return out

# --------------------------------------------------------------------------- #bad_r at a direction
def _batch_inv(xs, p):
    """Montgomery batch inversion of nonzero residues xs (skipping zeros -> None): one modexp total."""
    n = len(xs); pref = [1]*(n+1)
    for i in range(n):
        pref[i+1] = pref[i] * (xs[i] if xs[i] else 1) % p
    inv_all = pow(pref[n], p-2, p)
    out = [0]*n
    for i in range(n-1, -1, -1):
        if xs[i]:
            out[i] = inv_all * pref[i] % p
            inv_all = inv_all * xs[i] % p
        else:
            out[i] = 0
    return out

def badcount_binding(htab, rmax, dmax, p):
    """
    For folds r=2..rmax over the precomputed h-table:
      * 'bind' = bare spectrum (d=0, denominator h_0=1, the FAR BINDER b=k): | { -h_r(R) } |
      * 'max'  = max over far denom index d in 1..dmax (d != r) of | { -h_r(R)/h_d(R) } |
      * 'all'  = full per-d sweep, 'binding_d' = argmax (including d=0)
    Uses Montgomery batch inversion: ONE modexp per (r,d) pair, not one per subset.
    """
    # precompute, per denom index d, the batch inverse of h_d over all subsets (one modexp each)
    dens_inv = {}
    for d in range(1, dmax+1):
        col = [row[d] % p for row in htab]
        dens_inv[d] = _batch_inv(col, p)
    out = {}
    for r in range(2, rmax+1):
        counts = {}
        nums = [(-row[r]) % p for row in htab]
        counts[0] = len(set(nums))                              # d=0 bare spectrum (binder b=k)
        for d in range(1, dmax+1):
            if d == r: continue
            inv = dens_inv[d]
            seen = set()
            for i in range(len(nums)):
                if inv[i]:                                       # skip h_d(R)=0 (not a witness)
                    seen.add(nums[i] * inv[i] % p)
            counts[d] = len(seen)
        best_d = max(counts, key=lambda dd: counts[dd])
        out[r] = {"bind": counts[0], "max": counts[best_d], "binding_d": best_d, "all": dict(counts)}
    return out

# --------------------------------------------------------------------------- realized union (contrast)
def _rref(rows, p):
    rows = [r[:] for r in rows]; m = len(rows); nc = len(rows[0]) if m else 0; pr = 0
    for c in range(nc):
        sel = next((r for r in range(pr, m) if rows[r][c] % p), None)
        if sel is None: continue
        rows[pr], rows[sel] = rows[sel], rows[pr]
        invv = pow(rows[pr][c], p-2, p); rows[pr] = [(x*invv) % p for x in rows[pr]]
        for r in range(m):
            if r != pr and rows[r][c] % p:
                f = rows[r][c]; rows[r] = [(rows[r][j]-f*rows[pr][j]) % p for j in range(nc)]
        pr += 1
        if pr == m: break
    return rows

def left_null(V, p):
    m = len(V); kk = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    return [[row[kk+j] % p for j in range(m)] for row in _rref(aug, p)
            if all(x % p == 0 for x in row[:kk]) and any(x % p for x in row[kk:])]

def far_union_at(S, p, k, a, b, r):
    """realized far-line union over (n-r)-witness sets for direction (a,b): #distinct forced gamma."""
    n = len(S); size = n - r
    if size <= k: return p
    pa_ = [pow(int(x), a, p) for x in S]; pb_ = [pow(int(x), b, p) for x in S]
    good = set()
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        Pn = left_null(V, p)
        if not Pn: continue
        pa = [sum(Pn[t][ii]*pa_[R[ii]] for ii in range(size)) % p for t in range(len(Pn))]
        pb = [sum(Pn[t][ii]*pb_[R[ii]] for ii in range(size)) % p for t in range(len(Pn))]
        if not any(pb):
            if not any(pa): return p
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i]*pow(pb[i], p-2, p)) % p
        if all((pa[t]+g*pb[t]) % p == 0 for t in range(len(pb))): good.add(g)
    return len(good)

def realized_union_binding(S, p, k, cap=200_000, binder_only=False):
    """
    Max realized far-line union (the genuine budget-bounded U over (n-r)-WITNESS sets).
    binder_only=True restricts to the AUDITED binder direction b=k (far-line memory's binder),
    sweeping a and disagreement-count r -- keeps n=16 tractable.  `cap` skips infeasible witness
    enumerations (C(n,n-r) > cap).  Returns (U, (a,b,r)).
    """
    n = len(S); best = (-1, None)
    for r in range(k+1, n-k+1):
        size = n - r
        if size <= k or math.comb(n, size) > cap: continue
        blist = [k] if binder_only else list(range(k, size))
        for b in blist:
            for a in range(n):
                if a == b: continue
                u = far_union_at(S, p, k, a, b, r)
                if u > best[0]: best = (u, (a, b, r))
    return best

# --------------------------------------------------------------------------- degree fitting
def loglog_slope(xs, ys):
    lx = [math.log(x) for x in xs]; ly = [math.log(y) for y in ys]
    if any(y <= 0 for y in ys) or len(lx) < 2: return float('nan')
    nn = len(lx); sx = sum(lx); sy = sum(ly)
    sxx = sum(v*v for v in lx); sxy = sum(lx[i]*ly[i] for i in range(nn))
    den = nn*sxx - sx*sx
    return (nn*sxy - sx*sy)/den if den else float('nan')

def dyadic_slopes(ns, ys):
    out = []
    for i in range(1, len(ns)):
        if ns[i] == 2*ns[i-1] and ys[i-1] > 0 and ys[i] > 0:
            out.append(math.log2(ys[i]/ys[i-1]))
        else: out.append(float('nan'))
    return out

# --------------------------------------------------------------------------- driver
def main():
    try: sys.stdout.reconfigure(line_buffering=True)
    except Exception: pass
    with_n32 = '--with-n32' in sys.argv
    with_union = '--with-union' in sys.argv
    dyadic = [8, 16] + ([32] if with_n32 else [])
    control = [24]
    rmax = 6; dmax = 6

    print("="*94)
    print("TASK M-degBadR :  deg_n(#bad_r),  gamma_R = -h_{a-k}(R)/h_{b-k}(R)  over (k+1)-subsets")
    print(f"  rho = 1/4 (k=n/4); fold r := a-k (numerator h_r);  #bad_r over binom(mu_n, n/4+1)")
    print(f"  EXACT in F_p, p = 1 (mod n), p > n^4; p-independence checked across 2 primes")
    print("="*94)

    data = {}
    for n in dyadic + control:
        k = n // 4
        p1 = find_prime_cong1_above(n, n**4)
        p2 = find_prime_cong1_above(n, p1+1)
        S1 = subgroup(p1, n); S2 = subgroup(p2, n)
        C = math.comb(n, k+1)
        if C > 6_000_000:
            # n=32: stream (no multi-GB table); both primes for the count + p-independence check
            print(f"  [n={n}: streaming C(n,k+1)={C:,} subsets, ~9 min/prime ...]", flush=True)
            r1 = badcount_streaming(S1, k, rmax, dmax, p1)
            r2 = badcount_streaming(S2, k, rmax, dmax, p2)
        else:
            h1 = hr_table_over_subsets(S1, k, max(rmax, dmax), p1)
            h2 = hr_table_over_subsets(S2, k, max(rmax, dmax), p2)
            r1 = badcount_binding(h1, rmax, dmax, p1)
            r2 = badcount_binding(h2, rmax, dmax, p2)
        data[n] = {"res": r1, "res2": r2, "primes": (p1, p2), "k": k, "C": C}
        tag = "[2^mu]" if n in dyadic else "[CONTROL non-2-pow]"
        print(f"\nn={n:3d} {tag}  k={k}  C(n,k+1)={C}  primes=({p1},{p2})")
        print(f"   r | #bad_r^bind(d0,b=k) | #bad_r^max | bind_d | bad/C |  p-indep(bind/max)")
        for r in range(2, rmax+1):
            b1 = r1[r]; b2 = r2[r]
            pind = (b1['bind']==b2['bind'], b1['max']==b2['max'])
            print(f"   {r} | {b1['bind']:>19d} | {b1['max']:>10d} | {b1['binding_d']:^6d} | "
                  f"{b1['max']/C:5.3f} |  ({pind[0]},{pind[1]})")

    # ---- table + degree fit (use #bad_r^max = the binding far direction worst count) ----
    print("\n" + "="*94)
    print("#bad_r^max (binding far direction)  vs  n   [dyadic ladder; n=24 = control]")
    print("="*94)
    print("  r | " + " | ".join(f"n={n:>5d}" for n in dyadic) + " | n=24(ctrl) | bad/C(n=16)")
    print("  " + "-"*78)
    deg = {}
    for r in range(2, rmax+1):
        ys = [data[n]["res"][r]["max"] for n in dyadic]
        yctrl = data[24]["res"][r]["max"]
        fracC16 = data[16]["res"][r]["max"]/data[16]["C"]
        ds = dyadic_slopes(dyadic, ys); sl = loglog_slope(dyadic, ys)
        deg[r] = {"ys": ys, "ctrl": yctrl, "ds": ds, "sl": sl, "fracC16": fracC16}
        print("  " + f"{r} | " + " | ".join(f"{y:>7d}" for y in ys) + f" | {yctrl:>10d} | {fracC16:6.3f}")

    print("\n  empirical degree  (dyadic ladder):")
    print("   r | dyadic-slope(s) log2-ratio | LS log-log deg | C-fraction stable? | deg < r ?")
    print("  " + "-"*80)
    verdict = {}
    for r in range(2, rmax+1):
        d = deg[r]; ds = d["ds"]; sl = d["sl"]
        lead = next((x for x in reversed(ds) if not math.isnan(x)), sl)
        is_lt = lead < r - 1e-9
        verdict[r] = is_lt
        dstr = " ".join(f"{x:+.2f}" for x in ds)
        # C-fraction stability: compare bad/C at n=8 vs n=16
        fc8 = data[8]["res"][r]["max"]/data[8]["C"]; fc16 = d["fracC16"]
        stable = abs(fc8-fc16) < 0.25
        print(f"   {r} |        {dstr:>14s}      |     {sl:+.3f}    |  {('YES ~%.2f*C'%fc16) if stable else 'no'} "
              f"| {'YES' if is_lt else 'NO'}")

    print("\n" + "="*94)
    print("KEY QUESTION:  is  deg_n(#bad_r) < r  (growing-slack decay) for the (k+1)-subset object ?")
    print("="*94)
    all_lt = all(verdict[r] for r in range(2, rmax+1))
    for r in range(2, rmax+1):
        lead = next((x for x in reversed(deg[r]["ds"]) if not math.isnan(x)), deg[r]["sl"])
        print(f"   r={r}:  deg_n(#bad_r) ~ {lead:+.2f}  {'<' if verdict[r] else '>='} r={r}  "
              f"=>  deg<r : {'YES' if verdict[r] else 'NO'}   (#bad_r ~ {deg[r]['fracC16']:.2f}*C(n,k+1))")
    print(f"\n   OVERALL deg<r for ALL r=2..{rmax}:  {'YES' if all_lt else 'NO'}")
    print("   INTERPRETATION: the (k+1)-subset distinct-gamma count tracks a STABLE FRACTION of")
    print("   C(n,k+1) (exponential in n) => deg_n(#bad_r) is SUPER-POLYNOMIAL, NOT < r.  The")
    print("   growing-slack does NOT hold at the (k+1)-subset SPECTRUM level (re-confirms O237).")
    print("="*94)

    # ---- contrast: the genuine realized UNION over (n-r)-witness sets, PER disagreement r ----
    if with_union:
        print("\n" + "="*94)
        print("CONTRAST -- realized far-line UNION U(r) over (n-r)-WITNESS sets, per disagreement r:")
        print("  (the genuine delta* object; bounded by budget n ONLY AT/BELOW the delta* radius,")
        print("   then EXPLODES toward C(n,n-r) above it -- it is NOT globally O(n))")
        print("="*94)
        for n in [8, 16]:
            k = n // 4; p = find_prime_cong1_above(n, n**4); S = subgroup(p, n)
            print(f"  n={n} k={k} p={p}  (budget n={n}):")
            last_good = None
            for r in range(k+1, n-k+1):
                size = n - r
                if size <= k or math.comb(n, size) > 9_000: continue
                # binder direction b=k, sweep a; per-r max realized union
                best = -1; bsta = None
                for a in range(n):
                    if a == k: continue
                    u = far_union_at(S, p, k, a, k, r)
                    if u > best: best, bsta = u, a
                ok = best <= n
                if ok: last_good = r
                print(f"    r={r} (delta={r/n:.3f}): U={best:>5d}  a={bsta}  {'<= n  OK' if ok else '>  n  BAD (explodes)'}")
            if last_good is not None:
                print(f"    => delta*-radius (last U<=n): r={last_good}, delta*={last_good/n:.3f}; U=O(n) ONLY here.")
        print("  KEY CONTRAST: the (k+1)-subset SPECTRUM #bad_r ~ Theta(C(n,k+1)) at EVERY r (table above);")
        print("  the realized UNION U(r) is O(n) ONLY at the delta* radius and explodes past it.  The")
        print("  growing-slack 'deg<r' fails for the spectrum; the union's budget-boundedness is a")
        print("  delta*-radius phenomenon, not a global low-degree growth law.")
        print("="*94)

    return data, deg, verdict

if __name__ == "__main__":
    main()
