#!/usr/bin/env python3
"""
*** DEPRECATED v1 — DO NOT TRUST ITS NUMBERS. SUPERSEDED BY probe_dooriv_worstb_class_structure2.py ***

This v1 has TWO known defects (caught in codex review):
  (1) the QR-class axis is a SCAN ARTIFACT: it enumerates b=g^j and an even j makes b a QR by
      construction, so 'chi2(worst_b)=+1 always' is meaningless, not a real class bias.
  (2) for k>200000 (n=64,128) it scans only the FIRST 60k coset indices (a prefix), so its argmax +
      parity/residue distributions for large n are NOT representative of the whole quotient Z_k.
The AUTHORITATIVE, artifact-corrected result is in probe_dooriv_worstb_class_structure2.py, which (a)
works in the quotient Z_k coset-index arithmetic (not the ill-defined per-coset QR class), (b) samples
UNIFORMLY across the whole quotient for large k, and (c) excludes the Fermat zero-index v2 artifact.
v1 is kept ONLY as a record of the artifact that motivated v2. Its verdict text below is NOT reliable.

door-(iv) Lane 1 — IS THE WORST-b SET ITSELF MULTIPLICATIVELY STRUCTURED?

The brief's open question: "what arithmetic of b selects the worst coset alignment?
is the worst-b set itself structured?"

Distinct from:
 - 1e22ed805 worst-b QUOTIENT arithmetic (gcd/sublattice in the index quotient -> scattered)
 - 78d1df596 worst-b INTERNAL geometry (term participation -> generic EVT)
 - phase-set dilation invariance (a14578371)

THIS probe asks a NEW question: across structured primes and n, does argmax_b |eta_b|
land preferentially in a distinguished MULTIPLICATIVE CLASS of F_p^*?
Tested classes:
 (1) quadratic residue class of b           (chi_2(b) = +-1)
 (2) b's coset wrt the index-2 subgroup of the period quotient
 (3) 2-adic valuation v_2(ord_p(b)-related) — is b a 2-power-order element bias?
 (4) the multiplicative class b * (mu_n) — does worst-b avoid/prefer mu_n cosets?

eta_b = sum_{x in mu_n} e_p(b x),  mu_n = unique order-n subgroup of F_p^*.
PROPER subgroup: n = 2^a, p = structured prime with p == 1 mod n, p >> n^3 (prize regime).
EXACT integer arithmetic (no float wraparound). NEVER n = p-1.
"""
import cmath, math, sys

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(r-1):
            x = x*x % m
            if x==m-1: ok=True; break
        if not ok: return False
    return True

def find_primes(n, beta, count, start_mult=1):
    """primes p == 1 mod n, p ~ n^beta, p >> n^3. return list of distinct structured primes."""
    target = n**beta
    primes=[]
    k = max(1, (target // n) )
    # walk k upward so that p = k*n+1 is prime; collect 'count'
    seen=0
    kk = k
    while len(primes) < count and seen < 2_000_000:
        p = kk*n + 1
        if p > n**3 and is_prime(p):
            primes.append(p)
        kk += 1
        seen += 1
    return primes

def subgroup_mu_n(p, n):
    """generator of F_p^* then the order-n subgroup."""
    # find primitive root g
    def order_is_pm1(g):
        return pow(g, p-1, p) == 1
    # factor p-1 partially for primitive root test
    pm1 = p-1
    fs = set()
    m = pm1
    d = 2
    while d*d <= m:
        while m%d==0:
            fs.add(d); m//=d
        d += 1
    if m>1: fs.add(m)
    g = None
    for cand in range(2, p):
        if all(pow(cand,(pm1)//q,p)!=1 for q in fs):
            g = cand; break
    h = pow(g, (p-1)//n, p)   # generator of mu_n, order n
    mu = []
    cur = 1
    for _ in range(n):
        mu.append(cur)
        cur = cur*h % p
    return g, set(mu), mu

def eta_abs2(p, mu, b):
    """|eta_b|^2 exactly-ish: use cmath but b*x mod p is exact int; only the phase is float.
       For magnitude ranking this is fine (we only need argmax)."""
    s = 0j
    twopi_over_p = 2*math.pi/p
    for x in mu:
        ang = (b*x % p) * twopi_over_p
        s += cmath.exp(1j*ang)
    return (s.real*s.real + s.imag*s.imag)

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1

def run(n, beta=4, nprimes=4):
    primes = find_primes(n, beta, nprimes)
    print(f"\n=== n={n}, beta={beta}, primes={primes} (p>>n^3={n**3}) ===")
    qr_frac=[]; class2_frac=[]; mu_coset_repeat=[]
    for p in primes:
        g, muset, mu = subgroup_mu_n(p, n)
        # iterate b over ONE representative per mu_n-coset (the period quotient): b = g^j, j=0..(p-1)/n-1
        # too many for large n; cap the scan but make it a FULL scan when feasible
        k = (p-1)//n  # number of cosets
        reps = []
        cur = 1
        # g^j for j in 0..k-1 gives one rep per coset of mu_n? No: g^j ranges over all of F_p^*.
        # rep per coset of mu_n: take g^j for j=0..k-1 (since mu_n = <g^k>, cosets are g^j mu_n, j=0..k-1).
        gj = 1
        full = (k <= 200000)
        J = k if full else 60000
        worst_val = -1.0; worst_b = None; worst_j = None
        # also track distribution: collect top-T b's
        topT = []
        gpow = 1
        for j in range(J):
            b = gpow
            v = eta_abs2(p, mu, b)
            if v > worst_val:
                worst_val = v; worst_b = b; worst_j = j
            topT.append((v, b, j))
            gpow = gpow * g % p
        topT.sort(reverse=True)
        top = topT[:max(8, k//50 if full else 8)]
        # CLASS (1): quadratic residue class of worst-b and of the top set
        qr_top = [legendre(b,p) for (_,b,_) in top]
        qr_frac.append(sum(1 for s in qr_top if s==1)/len(qr_top))
        # CLASS (2): parity of j (coset index in the cyclic quotient Z_k): index-2 subgroup membership
        j_parity_top = [jj % 2 for (_,_,jj) in top]
        class2_frac.append(sum(j_parity_top)/len(j_parity_top))
        # CLASS (4): do top-b's repeat within a single mu_n coset? (they shouldn't if one-per-coset)
        cosets = set(jj for (_,_,jj) in top)
        mu_coset_repeat.append(len(cosets)/len(top))  # 1.0 = all distinct cosets
        M = math.sqrt(worst_val)
        ref = math.sqrt(n*math.log(p/n)) if p>n else 1
        print(f"  p={p}: M/sqrt(nlog)={M/ref:.3f}  worst_j={worst_j} (parity {worst_j%2})  "
              f"chi2(worst_b)={legendre(worst_b,p):+d}  k_cosets={k}  full_scan={full}")
        print(f"     top-set QR-frac={qr_frac[-1]:.3f}  j-parity-frac={class2_frac[-1]:.3f}  "
              f"distinct-coset-frac={mu_coset_repeat[-1]:.3f}")
    print(f"  >>> n={n} SUMMARY: mean QR-frac of top set = {sum(qr_frac)/len(qr_frac):.3f} (0.5=class-blind)")
    print(f"               mean j-parity-frac = {sum(class2_frac)/len(class2_frac):.3f} (0.5=index-2-blind)")
    return sum(qr_frac)/len(qr_frac), sum(class2_frac)/len(class2_frac)

if __name__ == "__main__":
    print("door-(iv) worst-b CLASS structure probe (exact int phases, proper mu_n, p>>n^3)")
    results=[]
    for n in [16, 32, 64, 128]:
        qr, j2 = run(n, beta=4, nprimes=4)
        results.append((n, qr, j2))
    print("\n================ VERDICT TABLE ================")
    print(" n   meanQRfrac  mean-jparityfrac   (both ->0.5 if worst-b is CLASS-BLIND)")
    for n,qr,j2 in results:
        print(f" {n:4d}   {qr:.3f}        {j2:.3f}")
    print("\nIf QR-frac and j-parity-frac BOTH hover ~0.5 with no n-trend, the worst-b set is")
    print("MULTIPLICATIVELY CLASS-BLIND => no class-restriction lever for door-(iv) anti-concentration.")
    print("If either locks to 0 or 1, the worst-b set IS structured => exploitable, FORMALIZE it.")
