#!/usr/bin/env python3
"""
probe_444_worstb_coherent_imbalance.py  (#444 / #464, door-(iv) Lane 1)

DECISIVE Lane-1 reconciliation: at the TRUE worst frequency b* (FULL coset-space scan, NOT sampled),
the two index-2 coset-halves of eta_b = sum_{y in mu_n} e_p(b*y) are:
  - COHERENT  (rho(b*) = 1 exactly; angle(A,B) = 0 to machine precision)  -> coset-half coherence
    supplies ZERO destructive interference (door-(iv) coherence route is dead), AND
  - STRICTLY IMBALANCED  (|A| != |B|; balance r(b*) bounded away from 1, NON-monotone in n).

This CORRECTS the earlier SAMPLED balance probe (scripts/probes/probe_dooriv_halfmass_balance.py),
whose "balance-enriched, r(b*) -> 0.93..0.9996" reading for n>=32 was a SAMPLING ARTIFACT: scanning
only ~4000 random cosets misses the true argmax and lands on a more-balanced near-max coset.

Consequence (formalized axiom-clean in
ArkLib/.../Frontier/_DoorIVWorstBCoherentImbalance.lean): under coherence with |A| != |B|,
   |A + B| < 2*max(|A|,|B|)   with gap  2*max - |A+B| = max - min > 0,
so the symmetric "/2" dyadic descent step (|A+B| = 2|A|, which needs |A|=|B|) is INAPPLICABLE at the
true worst frequency. The dyadic half-mass recursion the prize reduces to is genuinely ASYMMETRIC.

Probe-first, HONEST: PROPER 2-power subgroup mu_n < F_p^*, p == 1 mod n, p >> n^3, odd m=(p-1)/n,
NEVER n=q-1. The coset space F_p^*/mu_n ~ Z_m is scanned EXHAUSTIVELY over all m cosets via g^t.
HONESTY GUARD (codex P2): the probe REFUSES to emit a true-worst-b verdict for any (n,p) whose coset
count m exceeds the exhaustive cap (it would risk the very sampling artifact this probe refutes); such
rows print 'NON-EXHAUSTIVE - SKIPPED'. Reported rows (n=16/32/64, beta=4) all have m < cap = FULL scan.
NO moment, NO completion, NO Lean. Empirical only; claims hold for the (n,p) computed and reported.
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % n == 0: continue
        x = pow(a, d, n)
        if x == 1 or x == n-1: continue
        ok = False
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: ok = True; break
        if not ok: return False
    return True

def prim_root(p):
    phi = p-1; fac = set(); x = phi; d = 2
    while d*d <= x:
        while x % d == 0: fac.add(d); x //= d
        d += 1
    if x > 1: fac.add(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g

def find_prime(n, beta):
    target = int(round(n**beta)); k0 = max(2, target//n); best = None
    for dk in range(400000):
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

TWO_PI = 2*math.pi
def ep(a, p): return cmath.exp(1j*TWO_PI*(a % p)/p)

def analyze(n, beta, cap=600000):
    p = find_prime(n, beta)
    if p is None: return None
    g = prim_root(p); h = pow(g, (p-1)//n, p)
    powers = [pow(h, j, p) for j in range(n)]
    A_x = [powers[j] for j in range(0, n, 2)]   # mu_{n/2} (even powers of h)
    B_x = [powers[j] for j in range(1, n, 2)]   # coset h*mu_{n/2} (odd powers)
    m = (p-1)//n
    # HONESTY GUARD (codex P2): only report results that are EXHAUSTIVE over all m cosets.
    # A strided/sampled scan can MISS the true argmax and reproduce the exact sampling artifact
    # this probe exists to refute. So we REFUSE to emit a non-exhaustive verdict: if m exceeds the
    # exhaustive cap, return mode='NON-EXHAUSTIVE' and the caller must NOT claim a true-worst-b result.
    if m > cap:
        return dict(n=n, p=p, m=m, mode="NON-EXHAUSTIVE", exhaustive=False)
    reps = range(m); mode = "FULL"; exhaustive = True
    bestM = -1.0; best = None
    for t in reps:
        b = pow(g, t, p)
        A = sum(ep(b*x, p) for x in A_x)
        B = sum(ep(b*x, p) for x in B_x)
        Me = abs(A + B)
        if Me > bestM:
            bestM = Me; best = (b, A, B)
    b, A, B = best
    aA, aB = abs(A), abs(B)
    H = aA + aB
    rho = (abs(A+B)/H) if H > 0 else 0.0
    ang = abs(cmath.phase(A) - cmath.phase(B)); ang = min(ang, 2*math.pi-ang)
    r = (min(aA, aB)/max(aA, aB)) if max(aA, aB) > 0 else 0.0
    return dict(n=n, p=p, m=m, mode=mode, exhaustive=exhaustive, b=b, M=bestM, aA=aA, aB=aB,
                rho=rho, deficit=1-rho, angle=ang, balance=r,
                two_max=2*max(aA, aB), gap=2*max(aA, aB)-abs(A+B))

if __name__ == "__main__":
    print("=== probe_444_worstb_coherent_imbalance: COHERENT (rho=1) but IMBALANCED (r<1) at TRUE worst-b ===")
    print("    FULL coset scan F_p*/mu_n ~ Z_m via g^t; NOT sampled. coherence kills interference; imbalance breaks /2-descent")
    for (n, beta) in [(16,4.0),(32,4.0),(64,4.0)]:
        r = analyze(n, beta)
        if r is None: print(f"  n={n}: no prime"); continue
        if not r.get('exhaustive', False):
            print(f"  n={r['n']:3d} p={r['p']:>12d} m={r['m']:>8d} NON-EXHAUSTIVE (m>cap) — SKIPPED, no true-worst-b claim")
            continue
        print(f"  n={r['n']:3d} p={r['p']:>12d} m={r['m']:>8d} {r['mode']:<11} worst-b={r['b']}")
        print(f"      |eta|={r['M']:.4f} (sqrt n={math.sqrt(r['n']):.3f})  |A|={r['aA']:.4f} |B|={r['aB']:.4f}")
        print(f"      rho(b*)={r['rho']:.6f}  1-rho={r['deficit']:.2e}  angle(A,B)={r['angle']:.2e}rad  => COHERENT")
        print(f"      balance r(b*)={r['balance']:.4f} (<1 => IMBALANCED)  2*max={r['two_max']:.4f}  gap(2max-|eta|)={r['gap']:.4f}=max-min")
        ok = (r['deficit'] < 1e-6) and (r['balance'] < 0.999)
        print(f"      VERDICT: coherent-AND-imbalanced = {ok}  => symmetric /2-descent (needs r=1) INAPPLICABLE at true worst-b")
    print("=== done ===")
