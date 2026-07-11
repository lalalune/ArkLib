#!/usr/bin/env python3
"""
probe_407_loop44_smallgap_orbit_growth.py  (#444 -- the Loop44 POLY-orbit-count residual)

THE LANE (BridgeLoop44.lean, UNDER-VALUED on the board; NO DISPROOF entry on its small-gap residual):
  Loop43 (axiom-clean): the LITERAL prize closes iff the bad-challenge ORBIT count N is bounded:
     eps_mca = |V_delta|/q^2 <= N*S/q^2 <= N/q  (S=orbit size <= 2^m, using 2^m<=q).
  Loop44 (axiom-clean): the #232 prize is STRICTLY WEAKER than the constant-N conjecture Q2 -- it needs
     only a POLYNOMIAL bound N <= (2^m)^d. AND: "a polynomial orbit count is ALREADY A THEOREM in the
     Johnson range (poly(n) list size, GS/BCIKS 2025/2055), so the prize is UNCONDITIONAL above eta_0.
     The genuinely open residual is ONLY the small-gap band 0 < eta <= eta_0."
  => the ACTUAL open object is: in the SMALL-GAP band (radius just below Johnson), is the bad-orbit
     count N(n) POLYNOMIALLY bounded as n grows at the prize regime? probe_orbit_count_prize_regime
     found N<=5 for FAR pencils but only at n=8. NOBODY pushed N(n) to larger n with a GROWTH FIT + a
     rule-3 thinness gate. This does that -- the decisive Loop44 measurement.

OBJECT (exact, matches BridgeLoop43 V_delta / dilation-orbit semantics):
  mu_n = <g> proper 2-power subgroup of F_p* (m=(p-1)/n>1, NEVER n=q-1, prize prime p~n^4).
  Worst FAR monomial pencil (a,b), a,b>=k, far direction. At agreement band t (radius delta, t=ceil((1-delta)n)):
     bad-alpha set V = { alpha : exists t-subset S of mu_n with x^a+alpha*x^b agreeing with a deg<k poly on S }.
  The dilation z->h*z (h=gen of mu_n) acts on V by alpha -> alpha*h^{b-a} (codeword space dilation-invariant),
  orbits of size S = n/gcd(b-a,n). The ORBIT COUNT N = |V| / (orbit structure) = #distinct dilation-orbits of V.
  Loop43's N. Prize needs N <= poly(n).

MEASUREMENT (exact mod-p, PROPER mu_n, prize prime, NEVER n=q-1):
  For n = 8,16,32 (exact a-subset feasible), at the SMALL-GAP band (t = band just INSIDE Johnson, i.e.
  delta slightly below Johnson radius 1-sqrt(rho)), over the WORST far pencil (max |V| over far (a,b)):
    - |V| = #bad alpha   (the gamma count)
    - N = #dilation-orbits of V under alpha->alpha*h^{b-a}   (the Loop43 orbit count, the prize object)
    - orbit size S = n/gcd(b-a,n)
  Fit N(n) growth: poly (N ~ n^d, bounded d) vs super-poly. rule-3: THICK control (n non-2-power) -- if
  N is poly+thickness-invariant the orbit-count route is prize-viable but thin-blind (still closes via
  the unconditional poly theorem); if N thin << thick, thin HELPS; if N super-poly, the route is in doubt.

HONESTY: N is the Loop43 prize object; a poly fit SUPPORTS Loop44's poly-orbit-count route (the prize is
weaker than sqrt-cancellation). Exact small-n; the growth fit is reported with its honest n-range scope
(can't reach n=256). Python-only exact, no Lean => axiom-clean trivially.

RESULT (2026-06-15, opus-4-8 subagent) -- a WALL MAP, not a growth fit:
  n=8  small-gap band (t=5): NO far pencil has bad-alpha (V empty at that radius).
  n=16 small-gap band (t=7, rho=1/8): worst far pencil (9,5), |V|=5 bad-alpha, orbit size S=4,
       N = 2 dilation-orbits  (N/sqrt(16)=0.50). SMALL/bounded -- consistent with the existing
       probe_orbit_count_prize_regime N<=5 finding, now confirmed at the small-gap (just-below-Johnson)
       band specifically (Loop44's open residual band) with the exact bordered-Vandermonde engine.
  n>=32: BRUTE-WALLED. The small-gap band sits at agreement t ~ Johnson ~ sqrt(rho)*n ~ n/2, so the
       a-subset enumeration is C(n, ~n/2) (C(32,17)~5.6e8 PER pencil x many far pencils) = infeasible.
       This is the SAME c.348 wall ('numerics can't decide floor-vs-Johnson below n=256'): the small-gap
       ORBIT count cannot be brute-forced past n~16-18 either. A growth fit (poly vs super-poly) needs
       either the dilation-orbit-reduced enumeration pushed hard, or an analytic O(n) closed form.
  VERDICT (rule-4 wall map, rule-6 honest): at the only feasible small-gap point (n=16) the bad-orbit
  count N=2 is small, SUPPORTING (not proving) Loop44's poly-orbit-count route; the growth LAW is
  brute-walled at the Johnson-band subset explosion. Tool left for the next worker (the orbit-count
  engine is validated). CORE not closed.
"""
import itertools, math
from itertools import combinations
from collections import defaultdict


def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = 41
    while d*d <= m:
        if m % d == 0: return False
        d += 2
    return True


def prize_prime(n, beta):
    p = int(n**beta); p += (1 - p) % n
    while not (isprime(p) and (p-1) % n == 0): p += n
    return p


def _pf(n):
    f = set(); d = 2; m = n
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f


def find_gen(p, n):
    for h in range(2, p):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in _pf(n)):
            return x
    raise ValueError


def detmod(M, p):
    M = [row[:] for row in M]; nn = len(M); det = 1
    for col in range(nn):
        piv = next((r for r in range(col, nn) if M[r][col] % p), None)
        if piv is None: return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]; det = (-det) % p
        inv = pow(M[col][col], p-2, p); det = (det * M[col][col]) % p
        for r in range(col+1, nn):
            if M[r][col] % p:
                f = (M[r][col] * inv) % p
                for c in range(col, nn):
                    M[r][c] = (M[r][c] - f * M[col][c]) % p
    return det % p


def residual_xs(xs, k, yvals, p):
    M = []
    for a in range(k+1):
        M.append([pow(xs[a], j, p) for j in range(k)] + [yvals[a]])
    return detmod(M, p)


def bad_alphas(xvals, n, k, t, A, B, p):
    """Exact set of bad alpha for the monomial pencil u0=x^A, u1=x^B at agreement band t.
    alpha bad iff some t-subset S is aligned: all (k+1)-subtuples share alpha=-res0/res1 (non-deg)."""
    u0 = [pow(x, A, p) for x in xvals]
    u1 = [pow(x, B, p) for x in xvals]
    bad = set()
    for S in combinations(range(n), t):
        alpha = None; ok = True; nd = False
        for T in combinations(S, k+1):
            xs = [xvals[i] for i in T]
            r0 = residual_xs(xs, k, [u0[i] for i in T], p)
            r1 = residual_xs(xs, k, [u1[i] for i in T], p)
            if r1 % p == 0:
                if r0 % p != 0:
                    ok = False; break
                continue
            g = (-r0 * pow(r1, p-2, p)) % p
            nd = True
            if alpha is None: alpha = g
            elif g != alpha: ok = False; break
        if ok and nd and alpha is not None:
            bad.add(alpha)
    return bad


def orbit_count(bad, h, n, A, B, p):
    """#dilation-orbits of bad-alpha set under alpha -> alpha*h^{B-A}. orbit size = n/gcd(B-A,n)."""
    step = pow(h, (B - A) % n, p)  # multiplier
    seen = set(); orbits = 0
    for a in bad:
        if a in seen: continue
        orbits += 1
        x = a
        for _ in range(n):  # orbit closes within <= n steps
            if x in seen: break
            seen.add(x)
            x = (x * step) % p
    return orbits


def main():
    print("# Loop44: small-gap-band bad-ORBIT count N(n) growth -- does N stay poly(n)? (#444)")
    print("# N = #dilation-orbits of bad-alpha (Loop43 prize object). Prize needs N <= poly(n).")
    print("# WORST far pencil, agreement band JUST inside Johnson. PROPER mu_n, prize prime, NEVER n=q-1.\n")
    print(f"{'n':>4} {'k':>3} {'rho':>6} {'t(band)':>8} {'worst(A,B)':>11} {'|V|=#bad':>9} {'orbit S':>8} {'N=#orbits':>10} {'N/sqrt(n)':>9}")
    print("-" * 92)
    Ns_for_fit = []
    for n in (8, 16):
        beta = 4.0; k = max(2, n // 8)  # prize-ish proportional rate
        p = prize_prime(n, beta); h = find_gen(p, n)
        xvals = [pow(h, i, p) for i in range(n)]
        rho = k / n
        johnson_t = math.ceil((1 - (1 - math.sqrt(rho))) * n)  # t at Johnson radius = sqrt(rho)*n agreement
        # small-gap band = agreement just ABOVE Johnson agreement (radius just below Johnson)
        t = max(k + 2, johnson_t + 1)
        if t > n: t = n
        # scan FAR pencils (A,B>=k, A!=B, not correlated x^{n/2}); pick worst by |V|
        best = None
        for A in range(k, n):
            for Bb in range(k, n):
                if A == Bb: continue
                if (A % (n // 2) == 0) or (Bb % (n // 2) == 0):  # skip x^{n/2}-correlated
                    continue
                V = bad_alphas(xvals, n, k, t, A, Bb, p)
                if not V: continue
                if best is None or len(V) > best[0]:
                    N = orbit_count(V, h, n, A, Bb, p)
                    g = math.gcd((Bb - A) % n, n); S = n // g if g else n
                    best = (len(V), A, Bb, N, S)
        if best is None:
            print(f"{n:>4} {k:>3} {rho:>6.3f} {t:>8} {'(none far)':>11}")
            continue
        Vc, A, Bb, N, S = best
        Ns_for_fit.append((n, N))
        print(f"{n:>4} {k:>3} {rho:>6.3f} {t:>8} {f'({A},{Bb})':>11} {Vc:>9} {S:>8} {N:>10} {N/math.sqrt(n):>9.2f}")

    print("\n# GROWTH FIT (worst-pencil bad-orbit count N vs n):")
    if len(Ns_for_fit) >= 2:
        for i in range(1, len(Ns_for_fit)):
            n0, N0 = Ns_for_fit[i-1]; n1, N1 = Ns_for_fit[i]
            if N0 > 0 and N1 > 0:
                d = math.log(N1 / N0) / math.log(n1 / n0)
                print(f"#   n {n0}->{n1}: N {N0}->{N1}, local exponent d = {d:.2f}  (N ~ n^{d:.2f})")
    print("# READ: small bounded d (N ~ n^O(1)) => SUPPORTS Loop44's poly-orbit-count route (prize closes")
    print("#  on a weaker hypothesis than sqrt-cancellation). Super-poly/exploding N => route in doubt.")
    print("# (Loop44: poly N is ALREADY a theorem above Johnson; this probes the small-gap residual band.)")


if __name__ == '__main__':
    main()
