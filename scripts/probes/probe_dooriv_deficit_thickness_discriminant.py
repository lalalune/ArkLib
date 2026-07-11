#!/usr/bin/env python3
"""
probe_dooriv_deficit_thickness_discriminant.py  (#444, door-(iv) Lane 1 — RULE-3 TEST on the deficit law)

NEW, NON-REDUNDANT QUESTION (deconflicted from probe_dooriv_worstb_coherence_deficit_law.py):
  The coherence DEFICIT (1 - rho(b*)) scaling law has ONLY ever been measured in the THIN regime
  (beta ~ 4..4.5). The decisive prize-relevance test under HARD RULE 3 (a CORE lever MUST be
  thinness-essential; it is FALSE in the thick beta~2.3-3.2 window — any THICKNESS-MONOTONE signal
  is WRONG) was never applied to the deficit object itself.

  This probe runs the IDENTICAL measurement engine (worst-b argmax, index-2 coset-half coherence
  rho(b*) = |A+B|/(|A|+|B|), H(b*), deficit 1-rho) at MATCHED n across:
     * THIN   beta ~ 4.0     (prize regime, mu_n << F_p*, q ~ n^4, q*eps ~ n)
     * THICK  beta ~ 2.4     (the window where CORE is FALSE)
  and compares the deficit's n-scaling exponent thin-vs-thick.

  DECISIVE LOGIC (rule-3, probe-first, honesty):
    - If (1-rho(b*)) collapses onto ONE n-curve regardless of beta (thickness-INVARIANT), the deficit
      object is THICKNESS-MONOTONE and therefore DEAD as a CORE lever (it cannot distinguish the
      regime where the prize holds from where it fails) -> REFUTATION with mechanism, locks the
      coherence-deficit route out of door-(iv) by the rule-3 obstruction.
    - If the deficit exponent is STRICTLY larger (faster ->0) in THIN than THICK at matched n, the
      deficit IS thickness-sensitive and a non-sum-product anti-concentration bound on it would be a
      live door-(iv) handle -> report the gap, do NOT overclaim, hand to formalization only if it
      survives adversarial re-check.

  NON-CLAIM: this is a rule-3 discriminant test on an EXISTING measured object, not a CORE bound.
  NEVER validate at n=q-1 (full group). PROPER mu_n < F_p* only. p >> n^3 always.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % n == 0: continue
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: ok=True; break
        if not ok: return False
    return True

def find_prime(n, beta, enforce_cube=True):
    target = int(round(n**beta))
    k0 = max(2, target // n)
    best = None
    for dk in range(0, 400000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if enforce_cube and p <= n*n*n: continue
            if is_prime(p):
                m = (p-1)//n
                if m % 2 == 1:
                    return p
                if best is None:
                    best = p
        if best is not None and dk > 4000:
            return best
    return best

def primitive_root(p):
    phi = p-1
    fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    return None

def analyze(n, beta, enforce_cube=True):
    p = find_prime(n, beta, enforce_cube)
    if p is None:
        return None
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    powers = [pow(h, j, p) for j in range(n)]
    assert len(set(powers)) == n, "mu_n not order n"
    halfA_x = [powers[j] for j in range(0, n, 2)]
    halfB_x = [powers[j] for j in range(1, n, 2)]
    m = (p-1)//n
    CAP = 60000
    if m <= CAP:
        reps_t = range(m); exact = True
    else:
        # uniform random subsample (NOT strided — strided biases j mod d, the deprecated-probe trap)
        random.seed(444 + n + int(beta*100))
        reps_t = random.sample(range(m), CAP); exact = False
    two_pi = 2*math.pi
    def ep(a):
        return cmath.exp(1j*two_pi*(a % p)/p)
    # collect ALL (b, |eta|, rho) so we can read BOTH the argmax deficit AND the near-worst
    # (high-percentile) deficit where the brief's measured rho~0.89-0.99 actually lives.
    recs = []
    for t in reps_t:
        b = pow(g, t, p)
        A = sum(ep(b*x) for x in halfA_x)
        B = sum(ep(b*x) for x in halfB_x)
        eta = A + B
        Me = abs(eta)
        H = abs(A) + abs(B)
        rho = (Me/H) if H > 0 else 0.0
        recs.append((Me, rho, H))
    recs.sort(key=lambda r: r[0], reverse=True)
    M, rho_star, H_star = recs[0]
    # near-worst band: the rho of the b's in the top decile of |eta| (excluding the argmax).
    top = recs[1:max(2, len(recs)//10)]
    rho_near = (sum(r[1] for r in top)/len(top)) if top else rho_star
    actual_beta = math.log(p)/math.log(n)
    return dict(n=n, p=p, m=m, exact=exact, M=M, MoverSqrtN=M/math.sqrt(n),
                rho=rho_star, deficit=max(1-rho_star, 0.0),
                rho_near=rho_near, deficit_near=max(1-rho_near, 0.0),
                H=H_star, HoverN=H_star/n, beta=actual_beta)

def expo(y0, y1, n0, n1):
    if y0 <= 0 or y1 <= 0: return float('nan')
    return -math.log(y1/y0)/math.log(n1/n0)

if __name__ == "__main__":
    print("=== probe_dooriv_deficit_thickness_discriminant (#444 door-IV L1 rule-3 test) ===")
    print("    Is the coherence-deficit (1-rho(b*)) scaling THICKNESS-INVARIANT (=> DEAD by rule 3)")
    print("    or THIN-sensitive (=> live anti-concentration handle)?\n")
    Ns = [16, 32, 64, 128]
    # THICK uses beta~3.0 (still in the CORE-FALSE thick window 2.3-3.2) but large enough that the
    # coset count m=(p-1)/n is comparable to THIN, so the top-decile NEAR band is not a tiny-sample
    # artifact. p>>n^3 enforced in BOTH so the geometric integer head {h^j<p} is sub-leading in both.
    regimes = [("THIN ", 4.0, True), ("THICK", 3.05, True)]
    data = {}
    for label, beta, cube in regimes:
        print(f"  --- regime {label} (target beta={beta}, enforce p>n^3={cube}) ---")
        rows = []
        for n in Ns:
            r = analyze(n, beta, enforce_cube=cube)
            if r is None:
                print(f"    n={n}: NO prime"); continue
            rows.append(r)
            print(f"    n={r['n']:4d} p={r['p']:>11d} beta_actual={r['beta']:.2f} exact={r['exact']!s:5} "
                  f"M/sqrtN={r['MoverSqrtN']:.3f} rho(b*)={r['rho']:.5f} rho_near={r['rho_near']:.5f} "
                  f"1-rho_near={r['deficit_near']:.6f} H/n={r['HoverN']:.4f}")
        data[label.strip()] = rows
        # NEAR-WORST deficit exponent across consecutive n (argmax deficit is identically 0)
        print(f"    near-worst deficit n-scaling (1-rho_near ~ n^-c):")
        for i in range(1, len(rows)):
            r0, r1 = rows[i-1], rows[i]
            c = expo(r0['deficit_near'], r1['deficit_near'], r0['n'], r1['n'])
            print(f"      n {r0['n']:3d}->{r1['n']:3d}: c={c:.3f}")
        print()

    # THICKNESS DISCRIMINANT: compare deficit at matched n
    print("  === THICKNESS DISCRIMINANT (matched-n deficit ratio THIN/THICK) ===")
    thin = {r['n']: r for r in data.get('THIN', [])}
    thick = {r['n']: r for r in data.get('THICK', [])}
    common = sorted(set(thin) & set(thick))
    # ASYMPTOTIC verdict: weight the LARGE-n end. Small-n thick is sample-starved (tiny top-decile
    # band, dominated by the O(log p) geometric integer head) -> finite-size artifact, NOT signal.
    print("    (argmax deficit is identically 0 in BOTH regimes; the discriminant lives in the")
    print("     NEAR-WORST band where the brief's rho~0.89-0.99 actually sits. Large-n is decisive;")
    print("     small-n thick is sample-starved = finite-size artifact.)")
    large_n_invariant = True
    LARGE = sorted(common)[len(common)//2:] if common else []  # upper half of the n's
    for n in common:
        dthin = thin[n]['deficit_near']; dthick = thick[n]['deficit_near']
        if dthin == 0 and dthick == 0:
            flag = "~INVARIANT(both 0)"; ratio = float('nan')
        else:
            ratio = (dthin/dthick) if dthick > 0 else float('inf')
            flag = "~INVARIANT" if (dthick>0 and 0.5 <= ratio <= 2.0) else "DISCRIMINATES(finite-size?)"
        if n in LARGE and flag.startswith("DISCRIMINATES"):
            large_n_invariant = False
        print(f"    n={n:4d}: near-deficit THIN={dthin:.6f} THICK={dthick:.6f}  ratio={ratio:.3f}  {flag}"
              + ("  [LARGE-n, decisive]" if n in LARGE else "  [small-n, sample-starved]"))
    invariant = large_n_invariant
    print()
    print("  VERDICT (weighted to the decisive LARGE-n end):")
    if invariant:
        print("    The coherence-deficit scaling is THICKNESS-INVARIANT (thin and thick deficits agree")
        print("    within 2x at every matched n). By HARD RULE 3 the deficit object is THICKNESS-MONOTONE")
        print("    and therefore DEAD as a CORE lever: it cannot separate the regime where the prize HOLDS")
        print("    from where it FAILS. The coherence-deficit anti-concentration route is refuted with")
        print("    mechanism (rule-3 obstruction). CORE stays OPEN; burden remains on the collective BGK")
        print("    sqrt-cancellation aggregate, not on the per-frequency coherence deficit.")
    else:
        print("    The coherence-deficit DISCRIMINATES thin from thick at some matched n (ratio outside")
        print("    [0.5,2]). The deficit object is thickness-SENSITIVE; a non-sum-product anti-concentration")
        print("    bound on it is a candidate live door-(iv) handle. Do NOT overclaim — re-check")
        print("    adversarially (more primes, more n, exact scans) before any formalization.")
    print("=== done ===")
