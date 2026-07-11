"""
probe_wfLA_fixedindex_lambda2.py  (lane wf-LA: spectral lambda2 / near-Ramanujan-up-to-sqrt-log)

Question for #407 LA lane: at FIXED index m=(p-1)/n (the prize has m=2^128 FIXED, ODD), does the
structure n=2^mu, m odd give ANY effective handle on M(n)=lambda2(Cay(F_q,mu_n)) that the growing-
field effective-Katz no-go missed? The no-go was for GROWING field at fixed subgroup. Here we fix
the INDEX and vary n, holding the prize-relevant thin geometry (m fixed >> n).

We measure C(n,p) := M / sqrt(n * log(p/n)) across:
  (A) FIXED ODD INDEX m, varying n=2^mu over primes p=n*m+1 prime.
  (B) FIXED ODD INDEX m, fixed n, varying the PRIME (several primes with same (n,m) impossible
      since p=n*m+1 is determined; instead vary the cofactor structure of m by choosing different
      odd m of similar size).
  (C) The thin-regime band: only beta = log_n(p) >= 4 (prize), vs intermediate.

Headline targets:
  - Does C stabilize (=> effective near-Ramanujan-up-to-sqrt-log holds with an EXPLICIT constant)?
  - Is the worst-b structured (m | b? gcd(b,m)?) giving a fixed-index reduction?
"""
import math, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prize_workspace import Workspace, isprime

def Cfun(n, p, M):
    return M / math.sqrt(n * math.log(p / n))

def beta(n, p):
    return math.log(p) / math.log(n)

def primes_for_n_fixed_oddindex_band(n, m_lo, m_hi):
    """all ODD m in [m_lo,m_hi] with p=n*m+1 prime (gives fixed-ish index, varying prime)."""
    out = []
    for m in range(m_lo | 1, m_hi, 2):  # odd m only
        p = n*m + 1
        if isprime(p):
            out.append((m, p))
    return out

print("="*78)
print("(A) FIXED ODD INDEX FAMILY: for each n=2^mu, sweep odd m, record C and worst-b structure")
print("="*78)
print(f"{'n':>6} {'m(odd)':>8} {'p':>12} {'beta':>5} {'M':>8} {'M/sqrtn':>8} {'C':>6} {'argmax_b':>10} {'gcd(b,m)':>8}")
worst_C = {}
for mu in range(2, 8):  # n = 4..128
    n = 1 << mu
    # pick odd m near a few scales to keep p computable (< ~5e6 for FFT)
    cands = primes_for_n_fixed_oddindex_band(n, 3, min( (5_000_000//n), 40000))
    # sample ~8 spread across the range, prefer larger (thinner) ones
    if not cands: continue
    step = max(1, len(cands)//8)
    sample = cands[::step][:8] + cands[-2:]
    seen=set()
    for (m, p) in sorted(set(sample)):
        if p in seen: continue
        seen.add(p)
        W = Workspace(n, p)
        M = W.M
        b = int(np.argmax(W.mag2[1:])) + 1
        g = math.gcd(b, m)
        C = Cfun(n, p, M)
        worst_C[n] = max(worst_C.get(n, 0), C)
        if m in (sample[0], sample[-1]) or C == worst_C[n]:
            print(f"{n:>6} {m:>8} {p:>12} {beta(n,p):>5.2f} {M:>8.2f} {W.M_over_sqrt_n:>8.3f} {C:>6.3f} {b:>10} {g:>8}")
print("\nworst C per n (over the sampled odd-index primes):")
for n in sorted(worst_C): print(f"  n={n:>4}: worstC={worst_C[n]:.3f}")

print()
print("="*78)
print("(B) THIN PRIZE BAND ONLY (beta>=4): is C bounded by a small constant in the prize geometry?")
print("="*78)
print(f"{'n':>6} {'m':>10} {'p':>14} {'beta':>5} {'M/sqrtn':>8} {'C':>6}")
band_C = []
for mu in range(2, 7):
    n = 1 << mu
    # need beta>=4 => p>=n^4 => m=(p-1)/n >= n^3. Keep p < ~6e6 so n<=2^5=32 mostly.
    m_target = n**3
    if n*m_target > 6_000_000:
        # too big to FFT; record the constraint
        print(f"{n:>6} {'(n^3 too big for FFT: p~%.1e)'%(n*m_target):>34}")
        continue
    found=0
    for m in range(m_target|1, m_target*3, 2):
        p = n*m+1
        if isprime(p):
            W = Workspace(n, p); M = W.M; C = Cfun(n,p,M)
            band_C.append(C)
            print(f"{n:>6} {m:>10} {p:>14} {beta(n,p):>5.2f} {W.M_over_sqrt_n:>8.3f} {C:>6.3f}")
            found+=1
            if found>=3: break
if band_C:
    print(f"\n  thin-band C: min={min(band_C):.3f} max={max(band_C):.3f} mean={sum(band_C)/len(band_C):.3f}")

print()
print("="*78)
print("(C) WORST-b LOCALIZATION: is the argmax frequency b governed by index m? (fixed-index handle)")
print("    Test: does the worst b always lie in a coset of the index-m structure / have gcd pattern?")
print("="*78)
for (n, mlist) in [(16, [255, 511, 1023]), (32, [127, 255, 511])]:
    for m in mlist:
        p = n*m+1
        if not isprime(p): continue
        W = Workspace(n, p)
        mag2 = W.mag2.copy()
        order = np.argsort(mag2[1:])[::-1] + 1
        top = order[:8]
        gcds = [math.gcd(int(b), m) for b in top]
        gcds_n = [math.gcd(int(b), n) for b in top]
        print(f"n={n} m={m} p={p}: top8 b={list(top)}")
        print(f"     gcd(b,m)={gcds}   gcd(b,n)={gcds_n}   (m={m}={'odd' if m%2 else 'EVEN'})")
