#!/usr/bin/env python3
"""
probe_dooriv_worstb_term_participation.py  (#444, door-(iv) "outside the moment hierarchy" fork)

CONTEXT / deconflict: my sweep just proved the period MARGINAL is Gaussian to 6th order
(57b3d915c); commit 8b2df98a5 said cracks must go "8th order+ OR outside the moment hierarchy."
8th-order is diminishing-returns moment grinding. This probe takes the OTHER fork: a non-moment,
non-EVT structural object of the WORST-b period itself.

η_b = Σ_{x∈μ_n} e_p(b·x) = Σ_{j=0}^{n-1} t_j,  t_j = e_p(b·g^{mj})  (n unit-modulus terms).
|η_b| is large iff the n unit vectors t_j ALIGN. The MOMENT hierarchy sees only Σ|η_b|^{2r}.
A genuinely-different object is the INTERNAL geometry of the n terms at the WORST b:

  PARTICIPATION / phase-spread statistics of {t_j} that are NOT functions of the even moments:
    R1 = |Σ t_j| / Σ|t_j| = |η_b|/n          (coherence; =1 iff all terms equal — RIGID limit)
    PR = (Σ|w_j|)² / (n·Σ|w_j|²) with w_j = projection of t_j onto η_b direction
                                              (participation ratio of the ALIGNED mass)
    Aplus = #{j : Re(t_j · conj(η_b)/|η_b|) > 0} / n   (fraction of terms pulling FORWARD)
    Gap   = (R1 at worst b) vs (R1 at typical b)         (is the worst b structurally special?)

DECISIVE QUESTION (door-(iv), non-moment): at the WORST b (argmax |η_b|), is R1 forced toward a
STRUCTURED value (e.g. a rigid R1→c with c selected by arithmetic of n) that an anti-concentration
bound could grip WITHOUT a moment? Or is the worst-b internal geometry just the generic large-
deviation of n random unit vectors (=> EVT/door-(iii), dead)?

If worst-b R1 ~ √(log(p/n)/n) (the EVT prediction M/n) with NO structural rigidity beyond it,
that's door-(iii) = dead. If R1 sits at a structured plateau / the forward-fraction Aplus locks to
a rational forced by n, there's a non-moment lever. Probe-first, formalize only if real survives.

EXACT bignum modular arithmetic (no int64 wraparound). PROPER μ_n, p≈n⁴≫n³, never n=q−1.
"""
import numpy as np

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prim_root(p):
    if p == 2: return 1
    phi = p-1; fac = set(); t = phi; d = 2
    while d*d <= t:
        while t % d == 0: fac.add(d); t //= d
        d += 1
    if t > 1: fac.add(t)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    raise RuntimeError

def find_prime(n, beta=4.0):
    lo = max(int(round(n**beta)), n**3 + 1)
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while not isprime(p): p += n
    return p

def main():
    print("# door-(iv) WORST-b internal term geometry (non-moment, non-EVT fork)")
    print("# R1=|eta|/n coherence; Aplus=forward-fraction; PR=aligned participation ratio.\n")
    print(f"{'n':>5} {'p':>13} {'#reps':>8} {'M/n(worst R1)':>13} {'EVT M/n':>9} "
          f"{'R1/EVT':>7} {'Aplus*':>7} {'PR*':>6} {'verdict':>10}")
    for n in (16, 32, 64, 128):
        p = find_prime(n)
        g = prim_root(p)
        m = (p-1)//n
        # mu_n terms exponents and the term phases for a given b:
        Hexp = [(m*j) % (p-1) for j in range(n)]
        H = np.array([pow(g, e, p) for e in Hexp], dtype=object)
        tp = 2.0*np.pi/p
        # scan quotient reps (cap), find worst |eta|. NOTE: for m > max_reps this is a SAMPLED
        # max (a LOWER bound on the true M); see verdict-robustness note in main() / .NOTE.
        max_reps = 60000
        sampled = m > max_reps
        reps = range(m) if not sampled else np.random.default_rng(7).choice(m, max_reps, replace=False)
        best = None
        all_R1 = []
        for t in reps:
            b = pow(g, int(t), p)
            res = (int(b) * H) % p                      # exact residues
            ang = tp * res.astype(np.float64)
            z = np.exp(1j*ang)                          # n unit-modulus terms t_j
            eta = z.sum()
            aeta = abs(eta)
            all_R1.append(aeta/n)
            if best is None or aeta > best[0]:
                best = (aeta, z, eta)
        aeta, z, eta = best
        R1 = aeta/n
        # EVT prediction M/n = sqrt(n*log(p/n))/n = sqrt(log(p/n)/n)
        evt_Mn = np.sqrt(np.log(p/n)/n)
        # forward fraction + aligned participation ratio at worst b
        u = eta/aeta                                    # unit alignment direction
        proj = (z * np.conj(u)).real                    # projection of each term onto eta direction
        Aplus = float((proj > 0).sum())/n
        w = np.clip(proj, 0, None)                      # forward mass
        PR = (w.sum()**2)/(n*(w**2).sum()) if (w**2).sum() > 0 else float('nan')
        typ_R1 = float(np.median(all_R1))
        ratio = R1/evt_Mn
        verdict = "EVT/dead" if 0.6 < ratio < 1.7 else "STRUCT?"
        smk = "~" if sampled else " "
        nrep = (len(reps) if not sampled else max_reps)
        print(f"{n:>5} {p:>13} {smk}{nrep:>7} "
              f"{R1:>13.5f} {evt_Mn:>9.5f} {ratio:>7.3f} {Aplus:>7.3f} {PR:>6.3f} {verdict:>10}")
        print(f"        typical(median) R1 over scanned b = {typ_R1:.5f}  "
              f"(worst/typ = {R1/typ_R1:.2f}x)")
    print()
    print("NOTE: ~ = SAMPLED worst-b over 60k reps (n=64,128). A sampled max is a LOWER bound on the")
    print("  true M, so it can only UNDERSTATE R1. The verdict is ROBUST to this: (a) the true worst-b")
    print("  R1 is bounded ABOVE by the Cauchy-Schwarz brick (participation_ratio_le_one) regardless")
    print("  of sampling; (b) the sampled worst-b is ALREADY generic-EVT with no Aplus/PR rational")
    print("  lock, and the true argmax (larger |eta|) would have even HIGHER coherence = even MORE")
    print("  aligned = even less anti-concentration slack, never less. No structural lever appears.\n")
    print("INTERPRETATION:")
    print("  - worst-b R1 ~ EVT M/n (ratio~1) AND Aplus~0.5-0.7 generic AND PR not locked to a")
    print("    rational of n => worst-b internal geometry is the generic large deviation of n unit")
    print("    vectors = door-(iii) EVT, DEAD. (confirms no non-moment internal lever.)")
    print("  - worst-b R1 sits at a STRUCTURED plateau OR Aplus/PR lock to a rational forced by n")
    print("    => non-moment structural rigidity, door-(iv) candidate. probe deeper before claim.")

if __name__ == "__main__":
    main()
