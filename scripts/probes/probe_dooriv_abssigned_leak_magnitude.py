#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — QUANTIFY the |.|-leak magnitude (does the dead-door |.| discard MORE in thin?).

CONTEXT: the kernel 92159f260 (`_DoorIVSignedDeepSumAbsLeak.lean`) proved ABSTRACTLY that
    L_r := Sum_{b!=0} |eta_b|^r  -  |Sum_{b!=0} eta_b^r|   >= 0      (leak_nonneg)
i.e. the triangle inequality |Sum eta_b^r| <= Sum |eta_b|^r is the LEAK by which every moment/energy/
Wick/EVT packaging (all of which bound via Sum|eta_b|^r) discards the SIGNED deep cancellation that the
2026-06-21 prize-regime probe just showed is thinness-essential. The kernel left the MAGNITUDE of the
leak abstract. The open empirical question, directly extending the kernel:

  Is the leak FRACTION  f_r := L_r / Sum_{b!=0} |eta_b|^r  =  1 - |Sum eta_b^r| / Sum|eta_b|^r
  itself THINNESS-ESSENTIAL? i.e. does the |.| route throw away a LARGER fraction of the moment mass
  in the THIN prize regime than in the THICK window?

KEY CORRECTION (measured 2026-06-21): eta_b is REAL, so for EVEN r, eta_b^r = |eta_b|^r exactly
=> Sum eta_b^r = Sum|eta_b|^r and f_r == 0 identically. THE LEAK ONLY EXISTS AT ODD r, where eta_b^r
carries the sign and Sum_b eta_b^r genuinely cancels across b. So the |.|-leak (and the whole signed
deep-cancellation lever) is an ODD-r phenomenon. The dead-door moment route uses EVEN powers |eta_b|^{2r}
precisely because the even signed sum has nothing to cancel; the prize-relevant cancellation lives in the
ODD signed deep sums. This probe measures f_r at ODD r.

f_r in [0,1]. f_r ~ 0 => no cancellation, |.| loses nothing (the signed sum ~ the absolute sum: aligned).
f_r ~ 1 => the signed sum is tiny vs the absolute sum: |.| discards almost everything (strong signed
cancellation that the dead doors cannot see). If f_r is LARGER (closer to 1) in THIN than THICK and the
gap grows with depth r, that QUANTIFIES exactly how much more the dead-door methods leak in the prize
regime -- a sharp, kernel-backing, non-redundant measurement (the C_r probe measured |Sum eta_b^r|
normalized by M^r; THIS measures it normalized by the absolute MOMENT Sum|eta_b|^r, which is what the
dead doors actually use, so f_r is the literal fraction-discarded by the |.| step).

PROBE (probe-first, brief-compliant): PROPER mu_n (n=2^a), NEVER n=q-1, THIN beta>=4 (p>>n^3) vs THICK
beta~2.5, multiple structured primes, exact real arithmetic (eta_b real by negation-closure). even r.
"""
import math

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

def find_primes(t, mod, count):
    k0 = max(1, round(t/mod)); found=[]
    for d in range(0, 2000000):
        for s in (1,-1):
            kk = k0 + s*d
            if kk < 1: continue
            p = kk*mod + 1
            if p <= 3 or not is_prime(p): continue
            if p not in found:
                found.append(p)
                if len(found) >= count: return found
    return found

def subgroup(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    e=[]; x=1
    for _ in range(n):
        e.append(x); x=(x*h)%p
    return e

def periods(e, p):
    w = 2*math.pi/p
    cos = [math.cos(w*t) for t in range(p)]
    out=[0.0]*p
    for b in range(p):
        s=0.0
        for x in e: s += cos[(b*x)%p]
        out[b]=s
    return out

def leak_fraction_profile(n, p):
    e = subgroup(n, p); eta = periods(e, p)
    rmax = 2*int(math.log2(n)) + 3
    prof={}
    for r in range(3, rmax+1, 2):  # ODD r only: this is where the signed sum cancels (even r => f_r=0)
        absmom = 0.0; signed = 0.0
        for b in range(1, p):
            v = eta[b]
            absmom += abs(v)**r
            signed += v**r
        # f_r = 1 - |signed| / absmom  (fraction of moment mass killed by |.| at ODD r).
        prof[r] = 1.0 - (abs(signed)/absmom if absmom>0 else 0.0)
    return prof

def run():
    print("Door-(iv) |.|-leak FRACTION  f_r = 1 - |Sum eta_b^r| / Sum|eta_b|^r  at ODD r (discarded by |.|)")
    print("(even r => eta_b^r=|eta_b|^r => f_r=0 identically; the leak/cancellation is an ODD-r phenomenon.)")
    print("f_r~0: |.| loses nothing (aligned). f_r~1: |.| discards almost everything (strong signed cancel).")
    print("PROPER mu_n, NEVER n=q-1, multiple structured primes, exact real arithmetic. ODD r.\n")
    configs = [
        (16, [2.5, 2.6], [4.0, 4.3]),
        (32, [2.5, 2.6], [4.0, 4.2]),
        (64, [2.5],      [3.7]),
    ]
    results={}
    for n, thicks, thins in configs:
        results[n]={'thick':[], 'thin':[]}
        npr = 1 if n>=64 else 2
        for beta in thicks:
            for p in find_primes(int(round(n**beta)), n, npr):
                ab=math.log(p)/math.log(n); prof=leak_fraction_profile(n,p)
                results[n]['thick'].append(prof)
                print(f"  n={n:3d} THICK beta={ab:.2f} p={p:>9d}: "+" ".join(f"r{r}:{prof[r]:.4f}" for r in sorted(prof)))
        for beta in thins:
            for p in find_primes(int(round(n**beta)), n, npr):
                ab=math.log(p)/math.log(n); prof=leak_fraction_profile(n,p)
                results[n]['thin'].append(prof)
                print(f"  n={n:3d} THIN  beta={ab:.2f} p={p:>9d}: "+" ".join(f"r{r}:{prof[r]:.4f}" for r in sorted(prof)))
        print()
    print("="*68)
    print("THIN-minus-THICK leak fraction  Δf_r = avg(f_r thin) - avg(f_r thick)")
    print(" Δf_r > 0 => |.| discards MORE in thin (thinness-essential leak). growth in r => deepening.")
    print("="*68)
    for n in results:
        thick=results[n]['thick']; thin=results[n]['thin']
        if not thick or not thin: continue
        rs=sorted(set(thick[0].keys()) & set(thin[0].keys()))
        def avg(lst,r): 
            v=[p[r] for p in lst if r in p]; return sum(v)/len(v) if v else float('nan')
        print(f"  n={n:3d}: "+" ".join(f"r{r}:{avg(thin,r)-avg(thick,r):+.4f}" for r in rs))
    print()
    print("INTERPRETATION: Δf_r>0 growing in r => the |.| step (used by EVERY dead door) discards a larger")
    print(" fraction of moment mass in the prize regime, deepening with r. This QUANTIFIES the kernel's")
    print(" leak_nonneg (92159f260) as thinness-essential: the dead doors don't just leak, they leak MORE")
    print(" where the prize lives. Maps the lever; does NOT bound M (no CORE/cancellation/capacity claim).")

if __name__ == "__main__":
    run()
