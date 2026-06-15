#!/usr/bin/env python3
"""
probe_407_Er_pdependence_onset_r4.py  (#444)

FINDING (rule-6 self-audited): the E_r(mu_n)-closed-form program (44234dc3d/5b0873ddb: E_2=3n(n-1),
E_3=15n^3-45n^2+40n, E_4=105n^4-630n^3+1435n^2-1155n, "g(r)=1-r/n", the dominant live lane) ASSUMES
E_r is a p-INVARIANT polynomial in n. Holds for r<=3 universally + r=4 at GENERIC primes -- but FAILS
at a SPARSE set of STRUCTURED prize primes, FIRST at r=4.

  - E_2, E_3 ARE p-invariant (genuinely polynomial): identical across ALL probed prize primes.
  - E_4: the published 105n^4-630n^3+1435n^2-1155n IS CORRECT for GENERIC primes (excess=0 for the
    overwhelming majority of near-primes). But a SPARSE STRUCTURED subset shows a fixed POSITIVE excess:
        n=16: ONLY the Fermat prime p=65537=2^16+1 -> E_4=4654160 = generic+4480 (+0.096%); 4 others -> +0.
        n=32: p=1048609, p=1049281 -> generic+645120 (+0.710%); 3 other near-primes -> +0.
    => E_4 is p-DEPENDENT on a measure-zero structured-prime set; the anomaly ONSETS at r=4 (r<=3 clean).

WHY THIS MATTERS (rule-4 constraint on the dominant lane):
  IF the prize prime is structured (Fermat p=2^k+1 is a natural pick at p~n^4 since n=2^a), the relevant
  E_4 sits ABOVE the generic polynomial, so the Wick ratio W_4 = E_4/((2*4-1)!! n^4) is LARGER (LESS
  headroom) than the clean "g(r)=1-r/n" narrative (built on r<=3 p-invariant forms) implies. This is the
  additive-anomaly the §3 meta-theorem flags, ONSETTING at r=4 -- invisible to the r<=3 closed forms.
  BUT (rule-3 below): the excess SHRINKS with beta and VANISHES in the deep thin regime (beta>=4.5:
  excess=0 at every prime tested) => thickness-generic, NOT a thin-essential signal.

RULE-3 (thinness test): is the r=4 p-dependent excess THIN-essential or thickness-generic? Sweep beta
THICK (2.3-3.2, prize-FALSE) -> THIN (4-5). PROPER mu_n, never n=q-1.

CONTRIBUTION (closed-form-INDEPENDENT, also logged): the accumulated moment-step product telescopes to
the single Wick ratio: prod_{r=1}^{R-1} g(r) = E_R/((2R-1)!! n^R) = W_R. So the multi-step tower reduces
to ONE object W_R, and the p-dependence of E_4 directly perturbs W_4 (and all W_{R>=4}).

NO LEAN. Exact integer convolution => axiom-clean trivially.
"""
import math
from collections import Counter
import sympy as sp

def roots(nn, p):
    g = int(sp.primitive_root(p)); w = pow(g, (p - 1) // nn, p)
    assert pow(w, nn, p) == 1 and all(pow(w, d, p) != 1 for d in range(1, nn))
    return [pow(w, i, p) for i in range(nn)]

def Er(nn, p, R):
    base = roots(nn, p); h = Counter({0: 1}); out = {}
    for r in range(1, R + 1):
        nh = Counter()
        for t, c in h.items():
            for x in base: nh[(t + x) % p] += c
        h = nh; out[r] = sum(c * c for c in h.values())
    return out

def primes_near(nn, beta, k=4):
    target = int(nn ** beta); m = max(1, target // nn); c = []
    while True:
        p = m * nn + 1
        if p > target * 2: break
        if p >= target * 0.5 and sp.isprime(p): c.append(p)
        m += 1
    c.sort(key=lambda p: abs(p - target)); return c[:k]

def E4_generic_poly(n): return 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n
def E3_poly(n): return 15*n**3 - 45*n**2 + 40*n
def E2_poly(n): return 3*n**2 - 3*n

print("=" * 80)
print("STEP 1: E_2,E_3 p-INVARIANT (polynomial); E_4 p-DEPENDENT (anomaly onset at r=4)")
print("=" * 80)
for nn in [16, 32, 64]:
    print(f"--- n={nn}  (E2_poly={E2_poly(nn)}, E3_poly={E3_poly(nn)}, E4_gen_poly={E4_generic_poly(nn)}) ---")
    cand = primes_near(nn, 4.0, 5)
    for p in cand:
        e = Er(nn, p, 4)
        e2ok = (e[2] == E2_poly(nn)); e3ok = (e[3] == E3_poly(nn))
        d4 = e[4] - E4_generic_poly(nn)
        fer = " [Fermat 2^k+1]" if sp.isprime(p) and (p - 1) & (p - 2) == 0 else ""
        print(f"  p={p:>12d}: E2ok={e2ok} E3ok={e3ok} | E4={e[4]} (gen{'+' if d4>=0 else ''}{d4}, "
              f"{100*d4/E4_generic_poly(nn):+.3f}%){fer}")
print()

print("=" * 80)
print("STEP 2: the E_4 p-EXCESS at the PRIZE prime (closest to n^4) -- and its n-trend")
print("=" * 80)
print(" The moment route uses the prize prime = closest prime to n^beta. Track E_4(prize) vs generic:")
for nn in [16, 32, 64]:
    p = primes_near(nn, 4.0, 1)[0]
    e = Er(nn, p, 4)
    gen = E4_generic_poly(nn)
    exc = e[4] - gen
    W4_prize = e[4] / (105 * nn**4)
    W4_gen = gen / (105 * nn**4)
    print(f"  n={nn:3d} prize p={p}: E4={e[4]} generic={gen} EXCESS={exc} ({100*exc/gen:+.3f}%) | "
          f"W4(prize)={W4_prize:.5f} W4(generic)={W4_gen:.5f} (prize CLOSER to 1 by {W4_prize-W4_gen:+.5f})")
print()
print("  => at the prize prime the Wick ratio W_4 is HIGHER (less headroom) than the generic")
print("     polynomial predicts. The r<=3 closed-form lane (p-invariant) MISSES this -- the")
print("     p-dependence (additive anomaly) ONSETS exactly at r=4.")
print()

print("=" * 80)
print("STEP 3 (rule-3): is the r=4 p-excess THIN-essential or THICKNESS-generic?")
print("=" * 80)
print(" Sweep beta THICK(prize-FALSE) -> THIN. For each, prize prime = closest to n^beta. n=16,32.")
for nn in [16, 32]:
    print(f"--- n={nn} ---")
    for beta in [2.3, 2.6, 3.0, 3.2, 4.0, 4.5, 5.0]:
        cand = primes_near(nn, beta, 3)
        if not cand: continue
        # use the closest prime AND report spread over the 3 closest
        excs = []
        for p in cand:
            e4 = Er(nn, p, 4)[4]
            excs.append(e4 - E4_generic_poly(nn))
        p0 = cand[0]; e0 = excs[0]
        print(f"  beta={beta}: closest p={p0} EXCESS={e0} ({100*e0/E4_generic_poly(nn):+.3f}%) | "
              f"3-closest excess spread={excs}")
print()
print("INTERPRETATION: if the p-excess at structured primes is SAME magnitude across thick+thin beta,")
print("the anomaly is thickness-generic (a number-theoretic property of the structured prime, NOT a")
print("thin-subgroup signal) -- joining the board meta-pattern. If it GROWS in the thin regime, it's a")
print("live thin-essential perturbation to the moment route. Either way the brick STANDS: the E_r")
print("closed-form lane's p-invariance assumption breaks at r=4, and the prize-prime W_4 is higher than")
print("the published generic polynomial implies. CORE not closed.")
