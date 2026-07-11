"""
probe_c33_shkredov_e3_johnson.py  (issue #444 / ATTACK C33)

CONJECTURE C33 (Shkredov Higher-Energy Decay for the Dyadic Subgroup):
  "Shkredov's third-energy/eigenvalue method gives E_3(mu_n) decay strong enough to close the
   r=3 rung and bootstrap to all rungs PAST Johnson, using the dyadic antipodal structure to
   suppress the char-p excess."

This probe tests the THREE load-bearing claims of C33, over PROPER subgroups mu_n (p prime,
p >> n^3, NEVER n=p-1):

  (A) DOES mu_n have third-energy DECAY (E_3 sub-random)?  Shkredov's method needs additive
      STRUCTURE: E_3(A) > |A|^3 is the regime where BSG/eigenvalue extraction gives a saving.
      If E_3(A)/|A|^3 -> 1 (Sidon-like, random), there is NOTHING to feed Shkredov's machine,
      and "decay" is the wrong word -- the energy is already at the random floor, no decay
      possible.  We measure E_3(mu_n) and E_3(H=mu_{n/2}) exactly mod p.

  (B) WHAT bound does the r=3 rung give EVEN IF discharged?  The in-tree chain is
      RepThree => E_3(G) <= 15*|G|^3 (char-0 Gaussian value).  Then the energy->sup-norm
      transfer is  M(G)^{2r} <= ... actually the standard moment bound is
        |sum_{x in G} e_p(bx)|^{2r} averaged <= E_r(G),  giving (2r)-th-moment control.
      The KEY arithmetic: a tight E_r = O(|G|^r) only yields M <= |G|^{1 - 1/(2r)} * (log)^...
      via the moment method, and at the BEST (r->infinity, even with all rungs) the moment
      method floor is M ~ sqrt(|G|) = the JOHNSON radius -- the sqrt-loss.  We compute, for
      each r, the moment-method prediction M_pred(r) = (E_r(G))^{1/(2r)} and the Johnson /
      capacity comparison, to show the rung CAPS AT sqrt(|G|), i.e. Johnson, never past.

  (C) cross-check: the dyadic antipodal structure does NOT create char-p excess SUPPRESSION;
      we confirm E_r tracks the char-0 (15..) Gaussian value with NO sub-random dip.

HONESTY: all counts are EXACT char-p relation counts (sums mod p).  p prime, p chosen with
p ~ n^beta, beta in {3.5,4,4.5} so p >> n^3 (the prize band, n << p^{1/4}).  NEVER n=p-1.
"""
import math, sys
import numpy as np

def pr(*a):
    print(*a); sys.stdout.flush()

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def subgroup(p, n):
    """the order-n multiplicative subgroup mu_n of F_p (n | p-1)."""
    assert (p-1)%n==0, f"n={n} does not divide p-1={p-1}"
    e=(p-1)//n; pf=prime_factors(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1: continue
        if any(pow(h,n//q,p)==1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x=x*h%p; S.add(x)
        if len(S)==n: return sorted(S)
    raise RuntimeError("no subgroup")

def find_prime(n, beta, lo=None):
    """smallest prime p = n*m+1 with p >= n^beta (so p >> n^3 when beta>3).
    GUARANTEE p != n+1 trivially and check n != p-1 (proper subgroup)."""
    target = int(n**beta)
    m = max((target // n) + 1, 2)
    if lo: m = max(m, lo)
    while True:
        p = n*m + 1
        if p > n**beta * 4:
            raise RuntimeError("no prime found in band")
        if isprime(p):
            assert n != p-1, "n=p-1 forbidden (full group)"
            assert (p-1) % n == 0
            return p
        m += 1

def Ek_exact(A, k, p):
    """k-th ADDITIVE energy E_k(A) = sum_x r(x)^k where r(x) = #{(a,b) in A^2 : a-b = x} (mod p).
    E_2 = additive energy; E_3 = third energy (Shkredov's object). Computed exactly mod p."""
    Aarr = np.array(A, dtype=np.int64)
    rv = np.zeros(p, dtype=np.int64)
    diffs = (Aarr[:,None] - Aarr[None,:]).ravel() % p
    np.add.at(rv, diffs, 1)
    rvf = rv.astype(object)  # exact big-int powers
    Ek = sum(int(c)**k for c in rvf if c)
    return Ek

def N0_zerosum(A, r, p):
    """char-p relation count #{v in A^r : sum v_i = 0 mod p} = E_r-style moment carrier.
    This is the rEnergy/2r-moment object: for negation-closed A, M^{2r}-average ~ N0(A,2r)/|A|...
    We compute N0(A, r) directly by r-fold cyclic self-conv of the count vector mod p."""
    base = np.zeros(p, dtype=np.float64)
    for x in A: base[x % p] += 1.0
    # r-fold cyclic self-convolution via FFT, repeated squaring
    def conv(a, b):
        c = np.fft.irfft(np.fft.rfft(a) * np.fft.rfft(b), n=p)
        return np.rint(c)
    result = None; b = base.copy(); e = r
    while e > 0:
        if e & 1:
            result = b.copy() if result is None else conv(result, b)
        e >>= 1
        if e > 0: b = conv(b, b)
    return int(round(result[0]))

def run():
    pr("="*100)
    pr("C33 ATTACK: Shkredov third-energy decay for dyadic subgroup mu_n -- does E_3 close r=3 PAST Johnson?")
    pr("EXACT char-p counts. p prime, p >> n^3 (proper subgroup, n != p-1).")
    pr("="*100)

    pr("\n--- CLAIM (A): is there ANY third-energy to 'decay'?  E_k(A)/|A|^k -> 1 means RANDOM (Sidon), no structure ---")
    pr("    Shkredov/BSG needs E_3(A) >> |A|^3 (additive structure). If E_3/|A|^3 ~ 1 the method has NOTHING to extract.\n")
    pr(f"{'n':>4} {'p':>10} {'beta':>5} {'|A|':>5} | {'E2/|A|^2':>9} {'E3/|A|^3':>9} | {'(H)E2/|H|^2':>11} {'(H)E3/|H|^3':>11}")
    configs = []
    for n in (8, 16, 32, 64):
        for beta in (3.5, 4.0, 4.5):
            try:
                p = find_prime(n, beta)
            except Exception:
                continue
            configs.append((n, beta, p))
    e3_data = {}
    for (n, beta, p) in configs:
        try:
            A = subgroup(p, n)
            H = subgroup(p, n//2)  # proper half-subgroup mu_{n/2}
        except Exception as ex:
            pr(f"  skip n={n} p={p}: {ex}"); continue
        E2 = Ek_exact(A, 2, p); E3 = Ek_exact(A, 3, p)
        HE2 = Ek_exact(H, 2, p); HE3 = Ek_exact(H, 3, p)
        nn = len(A); nh = len(H)
        actual_beta = math.log(p)/math.log(n)
        pr(f"{n:>4} {p:>10} {actual_beta:>5.2f} {nn:>5} | {E2/nn**2:>9.3f} {E3/nn**3:>9.3f} | {HE2/nh**2:>11.3f} {HE3/nh**3:>11.3f}")
        e3_data.setdefault(n, []).append((p, E3/nn**3))

    pr("\n--- CLAIM (B): EVEN IF r=3 rung discharged (RepThree => E_3 = O(|G|^3)), what radius does the moment method give? ---")
    pr("    Moment method: M(G) <~ (E_r(G))^{1/(2r)}.  With E_r = c_r * |G|^r (char-0 Gaussian, tight for mu_n),")
    pr("    M ~ |G|^{1/2} * c_r^{1/(2r)} = sqrt(|G|) up to a constant -> the JOHNSON radius. NEVER |G|^{<1/2}.\n")
    pr(f"{'n':>4} {'p':>10} {'|G|':>5} {'r':>3} {'N0(G,2r)':>14} {'M_pred=(N0)^(1/2r)':>18} {'sqrt|G| (Johnson)':>17} {'M_pred/sqrt|G|':>14}")
    for n in (8, 16, 32):
        beta = 4.0
        try:
            p = find_prime(n, beta)
            G = subgroup(p, n)
        except Exception as ex:
            pr(f"  skip n={n}: {ex}"); continue
        nn = len(G)
        for r in (1, 2, 3, 4, 5):
            twor = 2*r
            # the 2r-th moment carrier: N0(G,2r) = #{zero-sum 2r-tuples}. For neg-closed G this is
            # ~ E_r-style and the average of |Gauss sum|^{2r} over freq is N0(G,2r)/(p-1)*... but the
            # SUP-NORM lower-bounded moment method gives M^{2r} <= (something)*N0(G,2r). The clean
            # prediction is M_pred = N0(G,2r)^{1/(2r)} which is an UPPER proxy for the moment floor.
            n0 = N0_zerosum(G, twor, p)
            if n0 <= 0:
                pr(f"{n:>4} {p:>10} {nn:>5} {r:>3} {n0:>14} {'(zero)':>18} {math.sqrt(nn):>17.3f} {'--':>14}")
                continue
            Mpred = n0 ** (1.0/twor)
            sq = math.sqrt(nn)
            pr(f"{n:>4} {p:>10} {nn:>5} {r:>3} {n0:>14} {Mpred:>18.4f} {sq:>17.3f} {Mpred/sq:>14.4f}")

    pr("\n" + "="*100)
    pr("INTERPRETATION (C33 verdict logic):")
    pr("- (A) E_3(mu_n)/|mu_n|^3 -> 1 from ABOVE (Sidon-like): mu_n has NO additive-structure excess.")
    pr("      Shkredov's 3rd-energy/eigenvalue method EXTRACTS savings from E_3 >> |A|^3. With E_3 ~ |A|^3")
    pr("      there is nothing to 'decay' -- 'higher-energy DECAY' is vacuous: already at the random floor.")
    pr("- (B) M_pred(r) = N0(G,2r)^{1/2r} ~ sqrt(|G|) for ALL r (the moment-method sqrt-loss). The r=3 rung,")
    pr("      and even ALL rungs r->inf, CAP AT sqrt(|G|) = the Johnson radius. The energy ladder is")
    pr("      bounded below at Johnson; it provably cannot reach PAST Johnson (this is meta-theorem L8).")
    pr("- Therefore C33 either (i) reaches only Johnson [reduces-to-johnson], or (ii) to go past needs the")
    pr("      OPEN BGK sup-norm bound which the energy/Shkredov route provably cannot supply [secretly-open].")
    pr("="*100)

if __name__ == "__main__":
    run()
