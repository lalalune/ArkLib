"""
#407 cumulant2power ATTACK + REFUTATION: is the cumulant explosion confined to a small
STRUCTURED (imprimitive-tower / O(log n)-coset) set of far frequencies, with the rest
sub-Gaussian (Wick)?

Setup (PRIZE regime: PROPER multiplicative subgroup G = mu_n <= F_p^*, large prime, multi-prime):
  eta_b = sum_{y in mu_n} psi(b y),  b in F_p,  psi standard additive char.
  Cumulant of order r:  K_r := sum_{b != 0} |eta_b|^{2r} = p*E_r(mu_n) - n^{2r}.
  Wick / real-Gaussian per-cumulant value:  WICK_r := p * (2r-1)!! * n^r.
  CumulantEnergyBound at r  <=>  K_r <= WICK_r  (>1 ratio == "explosion").
  eta_b is CONSTANT on cosets b*mu_n, so a "direction" = a coset of mu_n in F_p^*.

WHAT THIS PROBE FOUND (multi-prime, proper subgroups, n up to 256):

(1) The explosion happens ONLY at 2-power-structured primes (v2(p-1) >> v2(n), e.g. Fermat
    65537=2^16+1): there K_r/WICK_r -> {6.7, 1146, ...} for n in {32,64}. At generic primes
    (40961, 12289, 786433, 7340033) K_r/WICK_r <= ~1.5 (NO excess to control).

(2) WHEN it explodes, the excess IS extremely concentrated: 90% of K_r from < 1 coset, 99%
    from ~1-4 cosets (probe_cumulant_primitive_split: dir90/dir99 columns).

(3) BUT the carrying cosets are NOT a describable structured family:
    * NOT the imprimitive tower {b: v2(ord b) <= v2(n)} (the mu_n-sub-tower): for (65537,128)
      the explosion sits ENTIRELY in the complement (K_imp/WICK = 0.00 while K_tot/WICK = 264);
      its heaviest cosets b in {129, 33, 63, 3, 225, 7} have v2(ord b) in {15,11,16,16,13,16} =
      GENERIC multiplicative order, not imprimitive.
    * NOT additive-height: corr(min-coset-|b|, |eta_b|^2) in [-0.14, +0.11] ~ 0; for the larger
      generic primes the heaviest cosets have LARGE height (6747, 177881).
    The clean "concentrates on mu_n itself" observation is a coincidence of (65537, n<=64) where
    the moment-optimal r aligned with the subgroup; it BREAKS at n>=128 and at all other primes.

CONCLUSION (REFUTED): the cumulant explosion is NOT confined to the O(log n) imprimitive-tower
directions. It is (a) confined to ~O(1) cosets WHEN it occurs, but (b) those cosets are
prime-dependent and carry no uniform multiplicative/additive structural label -> the floor does
NOT reduce to a fixed finite structured set. This relocates the open core to the diffuse
incidence/additive-energy face (consistent with the line-ball-incidence wall), NOT a finite
imprimitive set. See DISPROOF_LOG.md entry 2026-06-14 (cumulant2power).
"""
import numpy as np
from math import gcd, log, sqrt, log2

def isprime(m):
    if m < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def fact2(k):
    r = 1
    for j in range(1, 2*k, 2): r *= j
    return r

def primitive_root(p):
    f = p-1; fs = set(); d = 2
    while d*d <= f:
        while f % d == 0: fs.add(d); f //= d
        d += 1
    if f > 1: fs.add(f)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g
    raise RuntimeError

def v2(m):
    v = 0
    while m % 2 == 0: m //= 2; v += 1
    return v

def analyze(p, n, rmax=8):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    mu = set(); x = 1
    for _ in range(n): x = (x*h) % p; mu.add(x)
    assert len(mu) == n
    mu_mask = np.zeros(p, bool)
    for x in mu: mu_mask[x] = True
    b = np.arange(p); eta = np.zeros(p, dtype=complex); ang = 2j*np.pi/p
    for x in mu: eta += np.exp(ang * ((b*x) % p))
    mag2 = np.abs(eta)**2

    vp = v2(p-1); vn = v2(n)
    # v2(ord b) for all b: largest j with b^{(p-1)/2^j}==1; v2ord = vp - j
    v2ord = np.zeros(p, dtype=int)
    for bb in range(1, p):
        j = 0
        while j <= vp and pow(bb, (p-1)//(2**j), p) == 1: j += 1
        v2ord[bb] = vp - (j-1)
    v2ord[0] = -1
    imp_mask = (v2ord >= 0) & (v2ord <= vn)   # imprimitive tower (incl mu_n)

    rstar = max(1, round(log(p)))
    rows = []
    for r in range(1, rmax+1):
        mr = mag2 ** r
        Ktot = mr[1:].sum(); Kmu = mr[mu_mask].sum(); Kimp = mr[imp_mask].sum()
        wick = p * fact2(r) * (n ** r)
        rows.append((r, Ktot/wick, Kmu/wick, Kimp/wick))
    # concentration of K_rstar: min #directions / #cosets carrying 90/99%
    mr = np.sort((mag2[1:]) ** rstar)[::-1]; tot = mr.sum(); cs = np.cumsum(mr)
    k90 = int(np.searchsorted(cs, 0.90*tot)) + 1
    k99 = int(np.searchsorted(cs, 0.99*tot)) + 1
    return vp, vn, rstar, rows, (k90, k99, k90/n, k99/n), mag2[1:].max()/n, bool(mu_mask[1+int(np.argmax(mag2[1:]))])

def findp(n, tgt, fermat=False, want_odd=True):
    if fermat:
        for k in range(int(log2(n))+1, 24):
            cand = 2**k + 1
            if cand >= tgt*n and isprime(cand) and (cand-1) % n == 0: return cand
        return None
    for m in range(tgt, tgt*12):
        p = n*m + 1
        if isprime(p):
            op = p-1
            while op % 2 == 0: op //= 2
            if (not want_odd) or op >= 3: return p
    return None

print("="*104)
print("CUMULANT PRIMITIVE/IMPRIMITIVE SPLIT (#407 cumulant2power)")
print("  Wick ratios: K_tot/W | K_{mu_n}/W | K_{imp tower}/W.  >1 == explosion.")
print("  CONC: min #cosets carrying 90%/99% of K_{r*}. argmax: heaviest coset in mu_n?")
print("="*104)
for n in [16, 32, 64, 128, 256]:
    print(f"\n########## n = {n}  (v2 n = {int(log2(n))}) ##########")
    for label, fermat, want_odd in [("2-POWER prime", True, False),
                                     ("GENERIC prime", False, True)]:
        p = findp(n, 32, fermat=fermat, want_odd=want_odd)
        if p is None or p > 8_000_000:
            print(f"  [{label}] no suitable p"); continue
        vp, vn, rstar, rows, (k90, k99, c90, c99), maxr, amu = analyze(p, n)
        print(f"  [{label}] p={p}  v2(p-1)={vp}  r*~lnp={rstar}  max|eta|^2/n={maxr:.2f}  "
              f"argmax_in_mu_n={amu}")
        print(f"     {'r':>2} {'K_tot/W':>10} {'K_mu/W':>10} {'K_imp/W':>10}  flag")
        for (r, kt, km, ki) in rows:
            flag = " EXPLODE" if kt > 1.2 else ""
            disc = " (excess NOT in imp tower!)" if (kt > 1.2 and ki < 0.5*kt) else ""
            print(f"     {r:>2} {kt:>10.3f} {km:>10.3f} {ki:>10.3f}{flag}{disc}")
        print(f"     CONC at r*={rstar}: 90% from {c90:.1f} cosets ({k90} dirs), "
              f"99% from {c99:.1f} cosets ({k99} dirs)")
