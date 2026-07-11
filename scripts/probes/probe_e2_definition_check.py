"""
PROBE: reconcile E_2. My generic char-0 additive energy gives E_2 = 2n(n-1)+n = n(2n-1).
Shaw's afdd84d8b claims E_2 = 3n(n-1) = (2*2-1)!! * (n)_2 (the falling-factorial leading form).
These differ. Find which DEFINITION yields each, to know if Shaw's anchor uses a different object.

Candidates for "E_r":
  (A) additive energy #{(a,b) in S^r x S^r : sum a = sum b}                 -> my probe (= 2n^2-n at r=2)
  (B) the SPECTRAL 2r-th moment sum_{b in F_p} |sum_{x in S} e_p(bx)|^{2r}  -> includes ALL b incl b=0
  (C) the DC-subtracted A_r = E_r - n^{2r}/p (Shaw's corrected object)
  (D) sum_{b != 0} |...|^{2r}  (the period-sum energy W_r, EXCLUDES b=0)

For a Sidon-to-high-order set, (B) over Z (no modulus) is not finite; but the COMBINATORIAL identity is:
   sum_{b} |sum_x e(bx)|^{2r} = (number of x with mod N) * #{2r-tuples balancing} ... 
The clean fact: sum_{b in Z_N} |sum_{x in S} e(bx/N)|^{2r} = N * #{(a,b): sum a = sum b} for S subset Z_N.
So the SPECTRAL energy = N * (additive energy). The PER-FREQUENCY-AVERAGED energy = additive energy (A).

Let me just compute (A) for r=2,3 and compare to 3n(n-1) and the Wick=(2r-1)!! n^r and the falling
(2r-1)!!(n)_r, to pin which "E_2" Shaw means.
"""
import math, random
from collections import Counter

def perm(n, k):
    p = 1
    for j in range(k):
        p *= (n - j)
    return p

def char0_energy(S, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[v + x] += m
        c = nc
    return sum(m * m for m in c.values())

random.seed(2)
print(f"{'n':>3} {'r':>2} {'E_A(addit)':>12} {'3n(n-1)/15n^3?':>14} {'Wick=(2r-1)!!n^r':>16} {'ff=(2r-1)!!(n)_r':>16}")
for n in [8, 12, 16]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    for r in [2, 3]:
        E = char0_energy(S, r)
        dfac = 1
        for i in range(1, 2 * r, 2):
            dfac *= i
        wick = dfac * n ** r
        ff = dfac * perm(n, r)
        marker = (3 * n * (n - 1)) if r == 2 else (15 * n ** 3)
        print(f"{n:>3} {r:>2} {E:>12} {marker:>14} {wick:>16} {ff:>16}")
    print()
print("ff = (2r-1)!!(n)_r is the FALLING-FACTORIAL leading form Shaw cites. Compare to additive E_A.")
print("If E_A != ff at r=2, then either Shaw's anchor uses a different energy OR my additive count differs.")
print("Note ff at r=2 = 3*n(n-1); additive E_A at r=2 = 2n^2-n. They differ => DIFFERENT objects.")
