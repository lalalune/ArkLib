#!/usr/bin/env python3
"""
probe_dooriv_phaseset_additive_smallball.py  (#444, door-(iv) Lane 1 — the brief's literal target)

The brief asks verbatim: "how spread is {b·x^m mod p}? Any Littlewood-Offord / Halász-type small-ball
bound for this phase set that does NOT route through multiplicative energy?"

DISTINCT from prior work:
  * ae2bc7e0b probed the b-SIDE set W_q = {b : |η_b| large} ⊆ ℤ_m (additively spread). NOT this.
  * 78d1df596 probed the COMPLEX phase ALIGNMENT (coherence/participation) at worst b. NOT additive.
This probes the ADDITIVE structure of the x-SIDE PHASE-RESIDUE SET S_b = {b·x mod p : x ∈ μ_n} ⊆ ℤ_p
(the n integer residues feeding the worst-b sum), and asks whether a small-ball / additive-energy
bound on S_b gives an η_b control that does NOT pass through MULTIPLICATIVE energy.

S_b = b·μ_n (mod p) is a multiplicative DILATE of the subgroup μ_n. Its ADDITIVE energy
  E⁺(S_b) = #{(a,b,c,d) ∈ S_b⁴ : a+b = c+d}
is dilation-INVARIANT (E⁺(b·μ_n) = E⁺(μ_n)), so it does NOT depend on b — the worst b cannot change
it. The decisive door-(iv) question: is E⁺(μ_n) SMALL (Sidon-like, → n², so {b·x} is additively
spread and a small-ball bound would give |η_b| ≲ √(n·something) NOT through mult-energy) or LARGE
(structured, → n³, additive structure that saturates)? And — critically — does any small-ball bound
derived from E⁺ BEAT the trivial √n / avoid the multiplicative-energy wall, or does it just reproduce
the Plancherel/EVT √(n log) ceiling?

We measure, EXACTLY (integer residues mod p, exact bignum):
  E⁺(μ_n)/n²         (additive-energy normalized; Sidon ⇒ → 1, structured ⇒ grows with n)
  |μ_n + μ_n|/n      (sumset doubling; Sidon ⇒ → n/2, structured ⇒ O(1))
  best small-ball ρ* = max_t #{x∈μ_n : b·x ∈ (t, t+p/K)} / n   (concentration in an arc; K=n)
  and the Halász/LO heuristic |η_b| ≲ √(n) · (additive-energy factor)  vs the measured M.

VERDICT logic (rule-5 honesty):
  - if E⁺(μ_n)/n² is BOUNDED (Sidon-like) AND the small-ball ρ* → 0, the phase set is additively
    spread — but then the Halász small-ball bound gives only |η_b| ≲ √(n·log) = the SAME EVT/√n
    ceiling (does NOT beat the wall, does NOT avoid it). Mapped: the additive-spread is REAL but the
    small-ball lever reproduces BGK, not beats it. dead-but-precise.
  - if E⁺(μ_n)/n² GROWS, the phase set is additively structured = a multiplicative-energy object in
    disguise (E⁺ of a multiplicative subgroup IS multiplicative energy) ⇒ routes through the dead
    mult-energy wall. dead.
Either branch is a mapped wall, not a lever. We report which, axiom-clean only if a real lemma lands.

EXACT bignum modular arithmetic. PROPER μ_n, p≈n⁴≫n³, never n=q−1.
"""
import numpy as np
from itertools import product

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

def additive_energy(S, p):
    """E+(S) = #{(a,b,c,d): a+b=c+d} = sum_t r(t)^2 where r(t)=#{(a,b): a+b=t}.
       computed via the sumset multiplicity histogram (exact)."""
    from collections import Counter
    c = Counter()
    S = list(S)
    for a in S:
        for b in S:
            c[(a+b) % p] += 1
    return sum(v*v for v in c.values())

def sumset_size(S, p):
    return len({(a+b) % p for a in S for b in S})

def main():
    print("# door-(iv) phase-set {b·x mod p} ADDITIVE structure / small-ball (brief Lane-1 verbatim)")
    print("# E+(mu_n) is dilation-invariant => worst-b cannot change it. Sidon? or structured?\n")
    print(f"{'n':>5} {'p':>13} {'E+/n^2':>9} {'|S+S|/n':>9} {'smallball rho*':>14} "
          f"{'M':>9} {'M/sqrt(n log)':>14} {'verdict':>12}")
    for n in (16, 32, 64):
        p = find_prime(n)
        g = prim_root(p)
        m = (p-1)//n
        H = [pow(g, (m*j) % (p-1), p) for j in range(n)]    # mu_n elements (exact ints)
        # additive structure of mu_n (= S_1; dilation-invariant so b-independent)
        Eplus = additive_energy(H, p)
        ss = sumset_size(H, p)
        # worst-b |eta| + its small-ball concentration rho*
        tp = 2.0*np.pi/p
        Harr = np.array(H, dtype=object)
        # EXHAUSTIVE worst-b scan (m <= ~262k at n<=64, feasible) so M/bestb are TRUE worst-case.
        # NB: the CORE claim (E+/|S+S|) is dilation-INVARIANT hence b-independent + exact regardless
        # of which b; only M/small-ball use bestb. We scan all reps to keep M exact too (codex P2).
        max_reps = 300000
        sampled = m > max_reps
        reps = range(m) if not sampled else np.random.default_rng(3).choice(m, max_reps, replace=False)
        bestM = 0.0; bestb = None
        for t in reps:
            b = pow(g, int(t), p)
            res = ((int(b) * Harr) % p).astype(np.float64)
            aeta = abs(np.exp(1j*tp*res).sum())
            if aeta > bestM:
                bestM = aeta; bestb = b
        # small-ball: max # of {b·x mod p} in an arc of length p/n (K=n windows)
        resb = sorted(int((bestb * h) % p) for h in H)
        K = n
        width = p / K
        # sliding-window max count over the circular residue set
        arr = np.array(resb + [r + p for r in resb])
        rho = 0
        j = 0
        for i in range(len(resb)):
            while arr[j] < arr[i] + width:
                j += 1
            rho = max(rho, j - i)
        rho_star = rho / n
        evt = np.sqrt(n * np.log(p/n))
        ratio = bestM / evt
        # Sidon-spread iff E+/n^2 is FLAT (bounded, not growing with n) AND |S+S|~n^2/2. A true Sidon
        # set has E+/n^2 -> 1; a multiplicative subgroup sits at a small CONSTANT (~3) that does NOT
        # grow => additively spread (Sidon-like up to a constant), NOT additively structured.
        struct = "add-structured" if Eplus/n**2 > 0.4*n else "Sidon-spread"
        smk = "~" if sampled else ""
        verdict = f"{struct}{smk}"
        print(f"{n:>5} {p:>13} {Eplus/n**2:>9.3f} {ss/n:>9.3f} {rho_star:>14.4f} "
              f"{bestM:>9.3f} {ratio:>14.4f} {verdict:>12}")
    print()
    print("NOTE: E+/|S+S| are EXACT and dilation-INVARIANT (b-independent) — proven axiom-clean in")
    print("  _DoorIVPhaseSetDilationInvariant.lean (addEnergy_smul_eq) — so the worst b cannot tune")
    print("  them; the small-ball lever is b-blind. M is the (now full-scan, n<=64) true worst-b sum.\n")
    print("INTERPRETATION (door-(iv) Lane-1 small-ball verdict):")
    print("  - E+(mu_n)/n^2 is DILATION-INVARIANT (independent of b): worst-b cannot tune additive")
    print("    structure. If Sidon-spread (E+/n^2 ~ O(1)) the small-ball bound gives |eta| <~ sqrt(n log)")
    print("    = the SAME EVT/Plancherel ceiling (reproduces BGK, does NOT beat it). If structured")
    print("    (E+/n^2 grows) it IS multiplicative energy in disguise (E+ of a mult. subgroup) => the")
    print("    dead mult-energy wall. Either way a mapped wall, NOT a non-moment lever.")

if __name__ == "__main__":
    main()
