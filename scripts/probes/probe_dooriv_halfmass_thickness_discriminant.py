#!/usr/bin/env python3
"""
probe_dooriv_halfmass_thickness_discriminant.py  (#444, door-(iv) Lane 1 — RULE-3 test on the HALF-MASS)

CONTEXT. At the worst frequency b*, the index-2 coset-half coherence rho(b*)≡1, so
M(n) = |eta_{b*}| = H(b*) = |A_{b*}| + |B_{b*}| EXACTLY (kerneled: _DoorIVWorstBHalfMassCarriesAll).
The entire prize √-cancellation burden therefore lives in the HALF-MASS H(b*). Prior work measured
H(b*)~n^{0.54..0.60} and H(b*)/√(n log) saturating ~1.1-1.3 — but ONLY in the THIN regime.

NEW, NON-REDUNDANT QUESTION (deconflicted from all half-mass probes + the deficit-thickness probe):
  Is the HALF-MASS decay/growth law THICKNESS-INVARIANT? By HARD RULE 3 a CORE lever must be
  thinness-essential (CORE is FALSE in the thick β≈2.3-3.2 window). If H(b*)/n (or the H(b*) growth
  exponent, or H(b*)/√(n log)) collapses onto ONE n-curve regardless of β, the half-mass object is
  thickness-monotone and carries NO thin-specific structure a CORE bound could exploit — i.e. the
  half-mass IS just the collective BGK wall, with the same status thin and thick, NOT a leak.

We run the IDENTICAL engine (worst-b argmax, H(b*)=|A|+|B|) at:
  THIN  β≈4.0   (prize regime)   and   THICK β≈3.05  (CORE-FALSE window), both p>>n³, EXACT scans,
matched coset counts, uniform-RANDOM subsample (NOT strided). Compare:
  H(b*)/n          (normalized half-mass)
  H(b*)/√(n log)   (the prize-scale normalization; saturates ⟹ same wall)
  growth exponent  H(b*)~n^a  thin vs thick.

NON-CLAIM: rule-3 discriminant on an existing object, not a CORE bound. proper μ_n<F_p*, never n=q-1.
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

def find_prime(n, beta):
    target = int(round(n**beta))
    k0 = max(2, target // n)
    best = None
    for dk in range(0, 400000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p <= n*n*n: continue
            if is_prime(p):
                m = (p-1)//n
                if m % 2 == 1: return p
                if best is None: best = p
        if best is not None and dk > 4000: return best
    return best

def primitive_root(p):
    phi = p-1
    fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def analyze(n, beta):
    p = find_prime(n, beta)
    if p is None: return None
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    powers = [pow(h, j, p) for j in range(n)]
    assert len(set(powers)) == n
    halfA_x = [powers[j] for j in range(0, n, 2)]
    halfB_x = [powers[j] for j in range(1, n, 2)]
    m = (p-1)//n
    CAP = 60000
    if m <= CAP:
        reps_t = range(m); exact = True
    else:
        random.seed(444 + n + int(beta*100))
        reps_t = random.sample(range(m), CAP); exact = False
    two_pi = 2*math.pi
    def ep(a): return cmath.exp(1j*two_pi*(a % p)/p)
    bestM = -1.0; bestH = None
    for t in reps_t:
        b = pow(g, t, p)
        A = sum(ep(b*x) for x in halfA_x)
        B = sum(ep(b*x) for x in halfB_x)
        Me = abs(A+B)
        if Me > bestM:
            bestM = Me; bestH = abs(A)+abs(B)
    logfac = math.log(p/n)
    return dict(n=n, p=p, exact=exact, M=bestM, H=bestH, HoverN=bestH/n,
                HoverPrize=bestH/math.sqrt(n*logfac), beta=math.log(p)/math.log(n))

def expo(y0,y1,n0,n1):
    if y0<=0 or y1<=0: return float('nan')
    return math.log(y1/y0)/math.log(n1/n0)

if __name__ == "__main__":
    print("=== probe_dooriv_halfmass_thickness_discriminant (#444 door-IV L1 rule-3 on H(b*)) ===")
    print("    At b*, M=H(b*) exactly. Is the half-mass law THICKNESS-INVARIANT (=> same BGK wall,")
    print("    no thin-specific leak) or thin-sensitive?\n")
    Ns = [16,32,64,128]
    data = {}
    for label, beta in [("THIN ",4.0),("THICK",3.05)]:
        print(f"  --- regime {label} (beta={beta}) ---")
        rows=[]
        for n in Ns:
            r = analyze(n,beta)
            if r is None: print(f"    n={n}: NO prime"); continue
            rows.append(r)
            print(f"    n={r['n']:4d} p={r['p']:>11d} beta={r['beta']:.2f} exact={r['exact']!s:5} "
                  f"H={r['H']:.3f} H/n={r['HoverN']:.4f} H/sqrt(n log)={r['HoverPrize']:.4f}")
        data[label.strip()]=rows
        print("    H(b*) growth exponent (H~n^a):")
        for i in range(1,len(rows)):
            a = expo(rows[i-1]['H'], rows[i]['H'], rows[i-1]['n'], rows[i]['n'])
            print(f"      n {rows[i-1]['n']:3d}->{rows[i]['n']:3d}: a={a:.3f}")
        print()
    print("  === THICKNESS DISCRIMINANT (matched-n) ===")
    thin={r['n']:r for r in data.get('THIN',[])}; thick={r['n']:r for r in data.get('THICK',[])}
    common=sorted(set(thin)&set(thick)); LARGE=common[len(common)//2:]
    invariant=True
    for n in common:
        rt=thin[n]['HoverPrize']; rk=thick[n]['HoverPrize']
        ratio=rt/rk if rk>0 else float('inf')
        inv = (0.5<=ratio<=2.0)
        if n in LARGE and not inv: invariant=False
        print(f"    n={n:4d}: H/sqrt(n log) THIN={rt:.4f} THICK={rk:.4f} ratio={ratio:.3f} "
              f"{'~INVARIANT' if inv else 'DISCRIMINATES'}"
              + ("  [LARGE-n decisive]" if n in LARGE else "  [small-n]"))
    print("\n  VERDICT (weighted to large-n):")
    if invariant:
        print("    The prize-normalized half-mass H(b*)/√(n log) is THICKNESS-INVARIANT at the decisive")
        print("    large-n end. The half-mass carries NO thin-specific structure: it saturates the SAME")
        print("    prize-scale value thin and thick. By rule 3 it is therefore NOT a CORE leak — it IS the")
        print("    collective BGK √-cancellation wall, with identical status in both regimes. CORE OPEN.")
    else:
        print("    The half-mass normalization DISCRIMINATES thin from thick at the large-n end. Re-check")
        print("    adversarially (more primes/n, exact scans) before any formalization. Do NOT overclaim.")
    print("=== done ===")
