#!/usr/bin/env python3
"""
FACET (#407) part 2: ENSEMBLE margin of the floor ratio R for MINIMAL-2-adic
(odd-m) prize primes as n grows, and the same for moderate-v2 primes, to see if
odd-m has a more stable / lower-margin R (toward proving R < 1 with margin).

For each n in {16,32,64}, sample K minimal-2-adic primes (v2(p-1)=log2 n, m odd)
near p ~ n^beta, and K moderate-v2 primes (v2 = log2 n + 2). Report mean R, max R,
and the empirical headroom (1 - max R).

R := M(n)/sqrt(2 n log p),  M = max_{b!=0} |sum_{x in mu_n} e_p(b x)|.

HONESTY: mu_n proper subgroup; v2 kept modest (not Fermat). Single primes are
noisy so we ensemble to estimate the true upper envelope of R.
"""
import sympy, cmath, math

def v2(t):
    v = 0
    while t % 2 == 0:
        t //= 2; v += 1
    return v

def musub(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)], g

def floor_M(n, p):
    G, g = musub(n, p)
    m = (p-1)//n
    w = 2*math.pi/p
    mx = 0.0
    rep = 1
    for c in range(m):
        s = sum(cmath.exp(1j*w*((rep*x) % p)) for x in G)
        a = abs(s)
        if a > mx:
            mx = a
        rep = (rep*g) % p
    return mx

def primes_with_v2(v, start, K):
    base = 2**v
    out = []
    m = max(1, (start - 1)//base)
    if m % 2 == 0:
        m += 1
    while len(out) < K:
        p = base*m + 1
        if sympy.isprime(p) and v2(p-1) == v:
            out.append(p)
        m += 2
        if m > 50_000_000:
            break
    return out

def run():
    BETA = 3.0
    K = 12
    for n in (16, 32, 64):
        a = int(round(math.log2(n)))
        start = int(n**BETA)
        print(f"\n===== n={n}, beta~{BETA}, p_start={start}, K={K} primes/class =====")
        for label, v in [("minimal-2adic(m-odd)", a), ("moderate-v2", a+2)]:
            ps = primes_with_v2(v, start, K)
            Rs = []
            for p in ps:
                M = floor_M(n, p)
                Rs.append(M/math.sqrt(2*n*math.log(p)))
            Rs.sort()
            mean = sum(Rs)/len(Rs)
            mx = Rs[-1]
            print(f"  {label:22s} v2={v}: meanR={mean:.3f} maxR={mx:.3f} "
                  f"headroom(1-maxR)={1-mx:+.3f}  [{'SOME R>1!' if mx>1 else 'all R<1'}]")
            print(f"      Rs sorted: {[round(r,3) for r in Rs]}")

# ============================== VERIFIED RESULTS (2026-06-14) ==============================
# Ensemble (K=12 primes/class) of floor ratio R = M/sqrt(2n log p), beta~3:
#   n=16: minimal-2adic meanR=0.685 maxR=0.721 | moderate-v2 meanR=0.717 maxR=0.758
#   n=32: minimal-2adic meanR=0.730 maxR=0.920 | moderate-v2 meanR=0.723 maxR=0.779
#   n=64: minimal-2adic meanR=0.729 maxR=0.850 | moderate-v2 meanR=0.745 maxR=0.816
#
# FINDINGS (honest):
#  - All sampled proper-subgroup primes give R < 1 (floor holds empirically in this regime).
#  - Mean R drifts UP slowly with n (0.68 -> 0.73) for BOTH classes; consistent with the
#    expected sqrt(log p) content, no sign of crossing 1 at these sizes but no proven margin.
#  - ODD-m is NOT more stable: the single LARGEST R in the whole sweep (0.920, n=32, p=32993,
#    m=1031 PRIME) is a MINIMAL-2-ADIC point. An odd-PRIME index m kills any Z/m subgroup
#    structure, so odd-m does not suppress the upper tail. [refutes odd-m stability advantage]
#  - The maxR (upper envelope) is noisy and does NOT order by v2; headroom (1-maxR) shows no
#    odd-m edge.
#
# VERDICT: odd-m advances NOTHING provable; the upper-tail control of R is exactly the BGK wall.
# ==========================================================================================

if __name__ == "__main__":
    run()
