"""
PROBE: exact closed form of the char-0 generic additive energy at r=3 (and the slack vs Wick).

Partitions of 3:  1^3, (2,1), (3).
  lambda=1^3:  orderings=3!=6,  ways=perm(n,3)/3! (3 equal mult-1 parts)  -> term = perm(n,3)/6 * 36 = 6*perm(n,3) = L_3.
  lambda=(2,1): orderings=3!/2!=3, ways=perm(n,2)/(1!*1!)=perm(n,2)  (one mult-2 group size1, one mult-1 group size1)
               -> term = perm(n,2) * 9.
  lambda=(3):  orderings=3!/3!=1, ways=perm(n,1)=n  -> term = n*1 = n.
So  E_3 = 6*n(n-1)(n-2) + 9*n(n-1) + n   (EXACT, generic char-0).
Wick_3 = (2*3-1)!! * n^3 = 15 n^3.
slack_3 = Wick_3 - E_3 = 15n^3 - 6n(n-1)(n-2) - 9n(n-1) - n.

Verify E_3 closed form against direct, and slack_3 >= 0.
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

def E3_closed(n):
    return 6 * n * (n - 1) * (n - 2) + 9 * n * (n - 1) + n

print("r=3 char-0 energy exact closed form  E_3 = 6 n(n-1)(n-2) + 9 n(n-1) + n:")
random.seed(21)
allok = True
for n in [6, 8, 12, 16, 20, 24]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    E = char0_energy(S, 3)
    Ec = E3_closed(n)
    wick3 = 15 * n ** 3
    slack3 = wick3 - Ec
    ok = (E == Ec)
    if not ok:
        allok = False
    print(f"  n={n:>3}: E_3(direct)={E:>12} E_3(closed)={Ec:>12} match={ok}  Wick_3={wick3:>12} slack_3={slack3:>10} slack>=0:{slack3>=0}")
print(f"  E_3 closed form exact for all tested: {allok}")
print()
# r=2 anchor (CORRECTED): the GENERIC char-0 additive energy is E_2 = 2n^2 - n, NOT 3n(n-1).
# 3n(n-1) = (2*2-1)!!*(n)_2 is the FALLING-FACTORIAL REFERENCE (= the actual subgroup value only for
# some (n,p), e.g. n=4,6,8 at large p; n=3,5 give the generic 2n^2-n; n=16 is p-dependent).
# See _SubgroupVsGenericEnergyReconcile + probe_e2_pdependence.py for the full honest accounting.
def char0_E2(S):
    return char0_energy(S, 2)
print("r=2 GENERIC anchor  E_2(generic) = 2n^2 - n  (NOT 3n(n-1); that's the falling-factorial reference):")
for n in [8, 12, 16]:
    S = sorted(random.sample(range(10 ** 7, 10 ** 9), n))
    E2 = char0_E2(S)
    print(f"  n={n}: E_2(generic)={E2}  2n^2-n={2*n*n-n}  match={E2==2*n*n-n}  [ff-ref 3n(n-1)={3*n*(n-1)}]")
