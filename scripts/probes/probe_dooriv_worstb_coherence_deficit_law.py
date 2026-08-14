#!/usr/bin/env python3
"""
probe_dooriv_worstb_coherence_deficit_law.py  (#444, door-(iv) Lane 1 — coherence-deficit SCALING LAW)

The brief's localized live object is rho(b*) = the index-2 coset-half COHERENCE at the worst frequency
b*: writing eta_{b} = A_b + B_b for the two index-2 coset-half partial period sums,
    rho(b) = |A_b + B_b| / (|A_b| + |B_b|)   in [0,1].
Two-piece triangle identity (axiom-clean, already in _DoorIVComplexRayCoherence):
    |eta_b| = rho(b) * (|A_b| + |B_b|).
So M(n) = |eta_{b*}| = rho(b*) * (|A_{b*}| + |B_{b*}|).

DECONFLICTION (distinct from all prior rho probes):
  * rho_asymptotic / rho_vs_order: char-0 MOMENT ratio R_r and ORDER-bucketing of rho. NOT the
    n-scaling of (1 - rho) at the worst b.
  * cosethalf_coherence / crosshalf_phase: measured rho at a FIXED n (rho ~ 0.89..0.99). Did NOT
    extract a SCALING LAW of the DEFICIT (1 - rho(b*)) across n=16..256.
  * sup_vs_sndmoment_slack: M/rmsM vs sqrt(log) = door-(iii) EVT (DEAD). This is door-(iv): the
    HALF-MASS (|A|+|B|) scale, NOT the second moment.

THE DECISIVE QUESTION (rule-5 honesty, probe-first):
  The half-mass H(b) = |A_b| + |B_b| is itself bounded by the trivial per-half ceiling: each half is a
  sum of n/2 unit phases so |A_b|,|B_b| <= n/2, giving H(b) <= n (trivial). The prize wants
  M <= C*sqrt(n log). With M = rho*H, a door-(iv) win needs EITHER
      (a) H(b*) << n  (the half-masses themselves are sqrt-cancelled — but that's just the SAME
          period-sum problem one level down: recursion/self-similarity), OR
      (b) rho(b*) -> 0 fast enough  (the two halves DESTRUCTIVELY interfere at the worst b).
  Lever A measured rho ~ +0.89..0.99 (NEAR 1 = halves ALIGN, NO destructive interference). If
  rho(b*) -> 1 as n grows, route (b) is DEAD and door-(iv) coherence cannot be the lever; the whole
  burden falls on H(b*), i.e. the recursion. If instead (1 - rho(b*)) has a non-trivial power law
  (1-rho ~ n^{-c}, c>0 but bounded away from making rho->0), measure whether rho(b*)*H_trivial(=n)
  could even in principle reach sqrt(n log) — i.e. does rho(b*) ~ sqrt(log/n)? If NOT, coherence
  alone is provably insufficient and the lever is the half-mass recursion (a REFUTATION with mechanism
  that localizes the prize OFF the coherence object and ONTO the self-similar half-mass descent).

We measure EXACTLY (PROPER mu_n < F_p*, p >> n^3, structured ODD-m primes, NEVER n=q-1):
  n, p, M=max|eta|, b*=argmax,
  rho(b*)           = |A+B|/(|A|+|B|)  at worst b
  H(b*)=|A|+|B|,    M/H = rho check,
  1 - rho(b*)       (the DEFICIT),
  rho_needed        = sqrt(n*log(p/n)) / n   (the rho the trivial half-mass ceiling H<=n would need
                      to reach the PRIZE bound; if rho(b*) >> rho_needed, coherence is INSUFFICIENT)
  H(b*)/n           (is the half-mass already sqrt-cancelled? if H/n -> 0 the recursion is doing
                      the work, not coherence)
and fit (1 - rho(b*)) ~ n^{-c} and rho(b*) vs rho_needed across n.
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % n == 0: continue
        x=pow(a,d,n); 
        if x==1 or x==n-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: ok=True; break
        if not ok: return False
    return True

def find_prime(n, beta):
    # p prime, p-1 divisible by n, p ~ n^beta, prefer odd m=(p-1)/n
    target = int(round(n**beta))
    # search p = k*n + 1 near target with m odd if possible
    k0 = max(2, target // n)
    best = None
    for dk in range(0, 200000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p <= n*n*n: continue   # enforce p >> n^3
            if is_prime(p):
                m = (p-1)//n
                # prefer odd m (structured)
                if m % 2 == 1:
                    return p
                if best is None:
                    best = p
        if best is not None and dk > 4000:
            return best
    return best

def subgroup(p, n):
    # mu_n = unique order-n subgroup of F_p*: g^((p-1)/n) for primitive root g
    # find a primitive root
    def primitive_root(p):
        phi = p-1
        # factor phi
        fac=set(); x=phi; d=2
        while d*d<=x:
            while x%d==0: fac.add(d); x//=d
            d+=1
        if x>1: fac.add(x)
        for g in range(2,p):
            if all(pow(g,phi//q,p)!=1 for q in fac):
                return g
        return None
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mu = []
    v = 1
    for _ in range(n):
        mu.append(v); v = v*h % p
    return mu, g

def analyze(n, beta):
    p = find_prime(n, beta)
    if p is None:
        print(f"  n={n} beta={beta}: NO prime found"); return None
    mu, g = subgroup(p, n)
    assert len(set(mu)) == n, "mu_n not order n"
    # split mu_n into two index-2 coset-halves under the order-2 quotient:
    # mu_n is cyclic order n; halve by the subgroup of squares (index 2): even vs odd powers of h
    # h = generator of mu_n; halfA = h^{even}, halfB = h^{odd}
    h = pow(g, (p-1)//n, p)
    powers = [pow(h, j, p) for j in range(n)]
    halfA_x = [powers[j] for j in range(0, n, 2)]
    halfB_x = [powers[j] for j in range(1, n, 2)]
    # sweep coset reps b: one per mu_n-coset of F_p* is enough since |eta| is coset-constant.
    # represent cosets by b in 1..(p-1), but that's m=(p-1)/n reps; for large p sample? No: be exact
    # but cap work. m=(p-1)/n. For n>=64, m can be huge. Cap by scanning b in a representative set:
    # scan all b in [1, p-1] is too big. Use: cosets are indexed by F_p*/mu_n ~ Z_m. Pick rep b = g^t
    # for t in 0..m-1? still m reps. To stay tractable, scan b=1..min(p-1, CAP) but that biases.
    # Correct tractable approach: enumerate coset reps as g^t, t=0..m-1, but cap m via stride.
    m = (p-1)//n
    # exact full scan only if m small; else strided sample (still gives a valid worst-b LOWER bound on M)
    CAP = 60000
    if m <= CAP:
        reps_t = range(m)
        exact = True
    else:
        stride = max(1, m // CAP)
        reps_t = range(0, m, stride)
        exact = False
    two_pi = 2*math.pi
    def ep(a):  # e_p(a) = exp(2pi i a / p)
        return cmath.exp(1j*two_pi*(a % p)/p)
    bestM = -1.0; best = None
    gt = 1  # g^0
    # precompute g^stride if strided
    for idx, t in enumerate(reps_t):
        b = pow(g, t, p)
        A = sum(ep(b*x) for x in halfA_x)
        B = sum(ep(b*x) for x in halfB_x)
        eta = A + B
        Me = abs(eta)
        if Me > bestM:
            bestM = Me; best = (b, A, B, eta)
    b, A, B, eta = best
    aA, aB = abs(A), abs(B)
    H = aA + aB
    rho = (abs(eta)/H) if H > 0 else 0.0
    M = bestM
    logfac = math.log(p/n)
    rho_needed = math.sqrt(n*logfac)/n   # rho the trivial H<=n ceiling would need for PRIZE
    return dict(n=n, p=p, m=m, exact=exact, M=M, MoverSqrtN=M/math.sqrt(n),
                rho=rho, deficit=1-rho, H=H, HoverN=H/n, rho_needed=rho_needed,
                Mover_rhoH=M/(rho*H) if rho*H>0 else float('nan'),
                logfac=logfac)

if __name__ == "__main__":
    print("=== probe_dooriv_worstb_coherence_deficit_law: does rho(b*) -> 1 (coherence DEAD) ===")
    print("    or does (1-rho) scale so coherence alone could reach the prize? rho_needed=sqrt(n log)/n")
    rows = []
    for (n, beta) in [(16,4.0),(16,4.5),(32,4.0),(32,4.5),(64,4.0),(128,4.0),(256,4.0)]:
        r = analyze(n, beta)
        if r is None: continue
        rows.append(r)
        print(f"  n={r['n']:4d} p={r['p']:>12d} m={r['m']:>9d} exact={r['exact']!s:5}  "
              f"M={r['M']:.4f} M/sqrtN={r['MoverSqrtN']:.3f}  rho(b*)={r['rho']:.5f} "
              f"1-rho={r['deficit']:.5f}  H/n={r['HoverN']:.4f}  rho_needed={r['rho_needed']:.5f}  "
              f"{'COHERENCE-INSUFFICIENT(rho>>needed)' if r['rho']>3*r['rho_needed'] else 'check'}")
    # scaling fits
    print("\n  --- scaling of deficit (1-rho) and H/n vs n ---")
    if len(rows) >= 2:
        import math as _m
        for i in range(1, len(rows)):
            r0, r1 = rows[i-1], rows[i]
            if r1['n'] == r0['n']: continue
            # power-law exponents
            def expo(y0,y1,n0,n1):
                if y0<=0 or y1<=0: return float('nan')
                return -_m.log(y1/y0)/_m.log(n1/n0)
            c_def = expo(r0['deficit'], r1['deficit'], r0['n'], r1['n'])
            c_H   = expo(r0['HoverN'],  r1['HoverN'],  r0['n'], r1['n'])
            print(f"    n {r0['n']}->{r1['n']}: (1-rho)~n^-{c_def:.3f}   (H/n)~n^-{c_H:.3f}")
    print("\n  VERDICT logic: if rho(b*) -> 1 (deficit -> 0) AND rho >> rho_needed at all n, then")
    print("  COHERENCE is provably INSUFFICIENT to reach the prize on its own (the halves ALIGN);")
    print("  the entire sqrt-cancellation burden is carried by H(b*)=|A|+|B| << n, i.e. the SELF-SIMILAR")
    print("  HALF-MASS RECURSION (each half is itself a thinner period sum). This LOCALIZES the prize")
    print("  OFF the coherence object and ONTO the descent — a refutation-with-mechanism for door-(iv) L1.")
    print("=== done ===")
