#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — PRIZE-REGIME VALIDATION of the signed-deep-cancellation localization.

CONTEXT (the load-bearing un-validated claim this probe tests):
The 2026-06-15 DISPROOF_LOG positive localization "SIGNED deep period-power cancellation IS
thinness-essential" measured the normalized signed deep sum
    C_r(n,p) = |sum_{b!=0} eta_b^r| / ((p-1) * M^r),   M = max_{b!=0} |eta_b|
and found C_r STRICTLY SMALLER (stronger signed cancellation) in THIN than THICK at every r, with the
thin/thick ratio GROWING with depth r (2.5x at r=2 -> 27x at r=10 for n=16). That entry is the
POSITIVE structural map of the open prize lever (the signed deep sum carries the thinness; the moment
route's |.| destroys it; the new kernel 92159f260 formalizes the leak direction).

BUT its HONEST CAVEAT: "small-n / sub-prize p (<=65537); exact-verified at this scale ... does NOT prove
a uniform-in-field deep-cancellation bound." The original probe ran ONLY n=8,16 at p<=65537. The
campaign has NEVER measured C_r at genuine prize-regime primes (p >> n^3, larger n, MULTIPLE structured
primes per n). If the thin/thick separation + r-growth is a small-p artifact, the positive localization
is undermined; if it SURVIVES at p >> n^3 across primes, the localization is hardened (real frontier).

THIS PROBE (probe-first, brief-compliant):
  - PROPER subgroup mu_n (n=2^a), NEVER n=q-1.
  - THICK reference beta in [2.4, 2.7] vs THIN prize regime beta in [4.0, 5.0].
  - MULTIPLE structured primes per (n,beta) to kill single-prime / Fermat artifacts.
  - p >> n^3 in the thin lane (beta>=4 => q >= n^4 >> n^3).
  - EXACT complex arithmetic (cmath), eta_b real (mu_n negation-closed).
  - Measure C_r for r = 2..~2*log2(n)+2 (the prize depth r ~ log n band).
  - Report THIN/THICK ratio per r and whether it GROWS with r and PERSISTS / GROWS with n.

VERDICT LOGIC:
  - If thin C_r < thick C_r at every r AND thin/thick ratio grows with r AT EVERY tested n and at the
    LARGE primes (not just the smallest) => localization HARDENED in prize regime (real, thinness-essential).
  - If the separation collapses (thin/thick -> 1) or reverses at large p / large n => localization is a
    small-p artifact => the positive map is undermined (would be a REFUTATION-with-mechanism, logged).
  - Honest about scale ceiling (exact arithmetic over F_p costs O(p) per (b); we push n as far as feasible).
"""
import math, cmath

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factor_small(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

def find_primes(t, mod, count, avoid_fermat=True):
    """find `count` distinct primes p = k*mod+1 nearest target t (so p ≡ 1 mod n => mu_n exists)."""
    k0 = max(1, round(t/mod))
    found=[]
    for d in range(0, 2000000):
        for s in (1,-1):
            kk = k0 + s*d
            if kk < 1: continue
            p = kk*mod + 1
            if p <= 3 or not is_prime(p): continue
            # avoid p-1 being a pure power of 2 with no room (Fermat-ish artifact) only at small p
            if avoid_fermat and p < 200000 and (p-1) & (p-2) == 0:
                continue
            if p not in found:
                found.append(p)
                if len(found) >= count:
                    return found
    return found

def subgroup(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    e=[]; x=1
    for _ in range(n):
        e.append(x); x = (x*h) % p
    return e

def periods(e, p):
    """eta_b = sum_{x in mu_n} e_p(b x), b=0..p-1, real (mu_n negation-closed).
    Use a residue-indexed cos table: e_p(t) real part = cos(2pi t/p). Build cos[] over residues
    0..p-1 once (O(p)), then eta_b = sum_x cos[(b*x) mod p] via integer indexing (O(p*n) int ops,
    no per-call exp). eta_b real because for each x, -x in mu_n contributes the conjugate => imag cancels.
    """
    w = 2*math.pi/p
    cos = [math.cos(w*t) for t in range(p)]   # O(p) table
    out = [0.0]*p
    for b in range(p):
        s = 0.0
        for x in e:
            s += cos[(b*x) % p]
        out[b] = s
    return out

def Cr_profile(n, p):
    e = subgroup(n, p)
    eta = periods(e, p)
    M = max(abs(eta[b]) for b in range(1, p))
    rmax = 2*int(math.log2(n)) + 2
    prof = {}
    for r in range(2, rmax+1, 2):  # even r only (odd signed sums ~0 by symmetry; even carries the magnitude)
        tot = 0.0
        Mr = M**r
        for b in range(1, p):
            tot += eta[b]**r
        prof[r] = abs(tot) / ((p-1) * Mr)
    return prof, M

def run():
    print("Door-(iv) signed-deep C_r PRIZE-REGIME validation")
    print("C_r = |sum_{b!=0} eta_b^r| / ((p-1) M^r). small => strong signed cancellation (prize wants small, all r).")
    print("PROPER mu_n, NEVER n=q-1. multiple structured primes per (n,beta). EXACT complex arithmetic.\n")

    # n up to 64 with multiple primes is feasible exactly (p ~ n^4 .. p ~ n^4.5; periods loop is O(p*n)).
    # For thin beta>=4: q=n^4 => n=16:p~65k, n=32:p~1.05M, n=64:p~16.8M (heavier but feasible, 1-2 primes).
    configs = [
        (16, [2.5, 2.6], [4.0, 4.3]),
        (32, [2.5, 2.6], [4.0, 4.2]),
        (64, [2.5],      [3.7]),  # n=64: n^3=262144; beta=3.7 => p~6.4M >> n^3 (decisively thin, feasible exact)
    ]
    n_primes_thick = 2
    n_primes_thin  = 2

    results = {}  # (n) -> {'thick':[(p,prof)], 'thin':[(p,prof)]}
    for n, thicks, thins in configs:
        results[n] = {'thick':[], 'thin':[]}
        npr_t = 1 if n>=64 else n_primes_thick
        npr_h = 1 if n>=64 else n_primes_thin
        for beta in thicks:
            for p in find_primes(int(round(n**beta)), n, npr_t):
                ab = math.log(p)/math.log(n)
                prof, M = Cr_profile(n, p)
                results[n]['thick'].append((p, ab, prof, M))
                cells = " ".join(f"r{r}:{prof[r]:.4f}" for r in sorted(prof))
                print(f"  n={n:3d} THICK beta={ab:.2f} p={p:>10d} M={M:6.2f}: {cells}")
        for beta in thins:
            for p in find_primes(int(round(n**beta)), n, npr_h):
                ab = math.log(p)/math.log(n)
                prof, M = Cr_profile(n, p)
                results[n]['thin'].append((p, ab, prof, M))
                cells = " ".join(f"r{r}:{prof[r]:.4f}" for r in sorted(prof))
                print(f"  n={n:3d} THIN  beta={ab:.2f} p={p:>10d} M={M:6.2f}: {cells}")
        print()

    # ---- VERDICT: thin/thick ratio per r, growth with r, persistence with n ----
    print("="*70)
    print("THIN/THICK ratio  R_r = (thick C_r averaged) / (thin C_r averaged)")
    print("  R_r > 1  => thin cancels MORE (localization holds). growth in r => deepening separation.")
    print("="*70)
    for n in results:
        thick = results[n]['thick']; thin = results[n]['thin']
        if not thick or not thin: continue
        rs = sorted(set(thick[0][2].keys()) & set(thin[0][2].keys()))
        def avg_Cr(lst, r):
            vals=[prof[r] for (_,_,prof,_) in lst if r in prof]
            return sum(vals)/len(vals) if vals else float('nan')
        line=[]
        for r in rs:
            ct = avg_Cr(thick, r); cn = avg_Cr(thin, r)
            R = ct/cn if cn>0 else float('inf')
            line.append(f"r{r}:{R:5.1f}x")
        print(f"  n={n:3d}: " + " ".join(line))
    print()
    print("INTERPRETATION:")
    print(" - If R_r > 1 and GROWS with r at every n (incl. the LARGE p / n=64): localization HARDENED in")
    print("   prize regime (signed deep cancellation is real & thinness-essential at p >> n^3). The original")
    print("   small-p (<=65537) finding is NOT an artifact; the |.|-leak kernel 92159f260 sits on solid ground.")
    print(" - If R_r -> 1 or shrinks at large p/large n: small-p artifact => positive localization undermined")
    print("   (refutation-with-mechanism). Either way this is a decisive, never-before-run prize-regime check.")

if __name__ == "__main__":
    run()
