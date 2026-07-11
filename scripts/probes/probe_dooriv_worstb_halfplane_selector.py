"""
PROBE (#444, door-(iv) Lane 1): is the prize-worst frequency b* selected by a
NON-DILATION-INVARIANT half-plane / interval-occupancy feature of {b*x^m mod p}?

MOTIVATION. The campaign meta-theorem (_DoorIVPhaseSetDilationInvariant) PROVES that every
fixed additive-linear count / fiber statistic of the phase set {b*x^m} is invariant under the
nonzero dilation b |-> lambda*b, hence b-BLIND: it cannot select the adversarial worst frequency.
The DISPROOF_LOG therefore localizes the live question to: "what arithmetic of b selects the
worst coset alignment?" Any surviving selector MUST be a feature that BREAKS under dilation.

The most basic dilation-NON-invariant feature is the position of the phase points relative to a
FIXED reference: the interval [0, p/2) vs [p/2, p) (equivalently the SIGN of the real part of
e_p(b*x^m), i.e. cos(2*pi*(b*x^m)/p) > 0). Dilation b->lambda*b rotates the residues b*x^m and
thus genuinely changes which side of the cut each point lands on. So the half-plane occupancy
imbalance
        HP(b) := | #{x in mu_n : (b*x^m mod p) in [0,p/2)} - n/2 |
(and its signed/real-part-mass cousins) is a legitimate candidate worst-b selector.

QUESTION. Does HP(b) (or the real-part mass R(b) = sum_x cos(2*pi*b*x^m/p)) CORRELATE with, or
co-locate the argmax of, the prize mass |eta_b| = |sum_x e_p(b*x^m)|? If a strong, prime-stable,
NON-dilation-invariant selector exists, it is a genuinely new door-(iv) lever. If the half-plane
occupancy is ITSELF delocalized / uncorrelated with |eta_b| (as the dilation-invariant features
were), that closes one more concrete selector and is a clean refutation-with-mechanism.

HONESTY.
 - PROPER thin 2-power subgroup mu_n (n=2^a), m=(p-1)/n, prize regime p ~ n^beta, beta~4, p >> n^3.
 - n=16: FULL F_p* scan for the GLOBAL argmax (no sampling). n=32,64: SAMPLED upper-bound proxies,
   labelled as such. Never n=q-1.
 - exact integer arithmetic for residues; cos evaluated in float ONLY for the real-mass cousin
   (the half-plane count HP is EXACT integer). Verdicts stated only for (n) actually computed.
 - reports correlation of HP(b) AND R(b) with |eta_b|/sqrt(n) over the scanned b, plus where the
   GLOBAL argmax sits in the HP / R distribution (rank percentile).
"""
import sys, math, random, cmath
from collections import Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= m: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def find_prime(amax, beta):
    n = 2**amax
    target = int(n**beta)
    mod = 2**amax
    start = (target//mod)*mod + 1
    for k in range(0, 400000):
        for cand in (start + k*mod, start - k*mod):
            if cand > n and is_prime(cand):
                return cand
    return None

def primitive_root(p):
    fac = []; pm = p-1; d = 2
    while d*d <= pm:
        if pm % d == 0:
            fac.append(d)
            while pm % d == 0: pm //= d
        d += 1
    if pm > 1: fac.append(pm)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

def subgroup(p, g, n):
    h = pow(g, (p-1)//n, p)
    S = []; cur = 1
    for _ in range(n):
        S.append(cur); cur = cur*h % p
    return S

def eta_abs2(bS, p):
    """|sum_{y in bS} e_p(y)|^2 via exact-ish real/imag float sum; returns |eta|."""
    re = im = 0.0
    two_pi_over_p = 2.0*math.pi/p
    for y in bS:
        ang = two_pi_over_p*y
        re += math.cos(ang); im += math.sin(ang)
    return math.hypot(re, im)

def halfplane_count(bS, p):
    """EXACT integer: #{y in bS : y in [0, p/2)} (y already reduced mod p, in 0..p-1)."""
    half = p//2
    return sum(1 for y in bS if y < half)

def realmass(bS, p):
    """sum_x cos(2*pi*y/p) = Re(eta_b). float."""
    two_pi_over_p = 2.0*math.pi/p
    return sum(math.cos(two_pi_over_p*y) for y in bS)

def pearson(xs, ys):
    nn = len(xs)
    mx = sum(xs)/nn; my = sum(ys)/nn
    sxx = sum((x-mx)**2 for x in xs)
    syy = sum((y-my)**2 for y in ys)
    sxy = sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    if sxx <= 0 or syy <= 0: return float('nan')
    return sxy/math.sqrt(sxx*syy)

def run_n(amax, beta, full_scan, sample_count, emit):
    n = 2**amax
    p = find_prime(amax, beta)
    g = primitive_root(p)
    mu = subgroup(p, g, n)              # the n-th roots = mu_n (the y^m image already; mu_n = <h>)
    sq = math.sqrt(n)
    emit(f"\n## n={n}  p={p}  (p/n^3={p/n**3:.2f}, p/n^4={p/n**4:.3f})  {'FULL' if full_scan else f'SAMPLED({sample_count})'}")

    # the phase set for frequency b is {b * z : z in mu_n}, z ranges over the n-th roots.
    # (mu_n IS the image x^m as x ranges over F_p*; standard campaign identity.)
    if full_scan:
        bs = range(1, p)
    else:
        random.seed(1234567 + amax)
        bs = random.sample(range(1, p), min(sample_count, p-1))

    best_eta = -1.0; best_b = None
    etas = []; hps = []; rms = []; bs_list = []
    for b in bs:
        bS = [ (b*z) % p for z in mu ]
        e = eta_abs2(bS, p)
        hp = abs(halfplane_count(bS, p) - n/2)   # half-plane imbalance |occupancy - n/2|
        rm = abs(realmass(bS, p))                # |Re(eta_b)|
        etas.append(e/sq); hps.append(hp); rms.append(rm/sq); bs_list.append(b)
        if e > best_eta:
            best_eta = e; best_b = b; best_hp = hp; best_rm = rm/sq

    corr_hp = pearson(hps, etas)
    corr_rm = pearson(rms, etas)
    # rank percentile of the GLOBAL argmax in the HP distribution (1.0 = argmax has the largest HP)
    rank_hp = sum(1 for h in hps if h <= best_hp)/len(hps)
    rank_rm = sum(1 for r in rms if r <= best_rm)/len(rms)
    # also: among the top-10 |eta| frequencies, what is their mean HP-rank?
    order = sorted(range(len(etas)), key=lambda i: etas[i], reverse=True)
    top = order[:max(1, len(etas)//100)]   # top 1%
    hp_sorted = sorted(hps)
    def hp_pct(v): return sum(1 for h in hps if h <= v)/len(hps)
    top_hp_rank = sum(hp_pct(hps[i]) for i in top)/len(top)

    emit(f"  scanned b: {len(etas)}")
    emit(f"  max |eta|/sqrt(n) = {best_eta/sq:.4f} at b*={best_b}")
    emit(f"  corr( HP(b)=|occupancy-n/2| , |eta|/sqrt(n) ) = {corr_hp:+.4f}")
    emit(f"  corr( |Re eta|/sqrt(n)      , |eta|/sqrt(n) ) = {corr_rm:+.4f}")
    emit(f"  half-plane imbalance HP at b*: {best_hp:.1f}  (rank pct in HP dist = {rank_hp:.3f}; 1.0=largest)")
    emit(f"  |Re eta|/sqrt(n)        at b*: {best_rm:.3f}  (rank pct in R dist  = {rank_rm:.3f})")
    emit(f"  mean HP-rank-percentile of the top-1% heaviest |eta| frequencies = {top_hp_rank:.3f}")
    return corr_hp, corr_rm, rank_hp

def main():
    def emit(*a):
        line = " ".join(str(x) for x in a)
        print(line); sys.stdout.flush()
    emit("# door-(iv) Lane 1 probe: is worst-b selected by a NON-dilation-invariant half-plane feature?")
    emit("# HP(b)=|#{b*z in [0,p/2)} - n/2| (EXACT int); R(b)=|Re eta_b| (float).")
    emit("# dilation b->lambda*b genuinely changes HP/R (unlike all additive counts) -> legit candidate selector.")
    beta = 4.0
    results = []
    results.append(("n=16 FULL", run_n(4, beta, True, None, emit)))
    results.append(("n=32 SMP", run_n(5, beta, False, 4000, emit)))
    results.append(("n=64 SMP", run_n(6, beta, False, 4000, emit)))

    emit("\n## VERDICT")
    emit("If corr(HP,|eta|) and corr(R,|eta|) are STRONG (|.|>~0.6) and prime/n-stable, and the global")
    emit("argmax sits near the TOP of the HP/R distribution (rank pct ~1.0), then a non-dilation-invariant")
    emit("half-plane selector exists -> NEW door-(iv) lever to formalize. If they are WEAK / the argmax is")
    emit("delocalized in HP/R, the basic interval-occupancy feature ALSO fails to select the adversary, and")
    emit("the worst-b selector (if any) must be subtler than first-order half-plane occupancy. Honest either way.")

if __name__ == "__main__":
    main()
