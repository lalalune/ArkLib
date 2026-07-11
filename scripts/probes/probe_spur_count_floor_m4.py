"""Honest count of weight-4 antipodal-free collisions at m=4 (mu_16), p=17.
Spur_2(p) counts antipodal-free relations T with |T|<=4 and p | N(sigma_T). We must be careful:
- rotations T -> T+s (mod 16) give DIFFERENT exponent sets but the SAME norm up to a unit zeta^s
  multiple, so N(sigma_{T+s}) = N(sigma_T) (norm is rotation-invariant): they all collide together.
- We report BOTH the rotation-orbit count (distinct relations) and the per-orbit size, so any Lean
  count-floor claim is honest about what is genuinely distinct vs a rotation image.
"""
import sympy as sp
from sympy import symbols, Poly, GF, cyclotomic_poly
from itertools import combinations

X = symbols('X')
p = 17
m = 4
N = 1 << m  # 16
half = N >> 1  # 8

def antipodal_free(T):
    s = set(T)
    return all(((i + half) % N) not in s for i in T)

def collides(T):
    Phi = Poly(cyclotomic_poly(N, X), X, domain=GF(p))
    R = Poly(sum(X**i for i in T), X, domain=GF(p))
    return Phi.gcd(R).degree() >= 1

# all antipodal-free 4-subsets that collide at p=17
colliders = []
for T in combinations(range(N), 4):
    if antipodal_free(T) and collides(list(T)):
        colliders.append(T)

print(f"total antipodal-free weight-4 subsets colliding at p=17, m=4: {len(colliders)}")

# group into rotation orbits (T ~ T+s mod 16)
def canon(T):
    best = None
    for s in range(N):
        rt = tuple(sorted((i+s) % N for i in T))
        if best is None or rt < best:
            best = rt
    return best

orbits = {}
for T in colliders:
    orbits.setdefault(canon(T), []).append(T)
print(f"distinct ROTATION ORBITS among colliders: {len(orbits)}")
for c, members in sorted(orbits.items())[:12]:
    print(f"  orbit rep {c}: size {len(members)}")

# The honest minimal claim: at least one collider exists per nonempty orbit.
# A clean count-floor for Lean: the SINGLE canonical rep {0,1,2,4} collides (already shipped),
# plus we can state the rotation-image corollary: zeta^s * sigma also vanishes => Spur counts the
# whole orbit. Report orbit size of {0,1,2,4}:
c0 = canon((0,1,2,4))
print(f"\norbit of (0,1,2,4): rep {c0}, size {len(orbits.get(c0, []))}")
print("=> Spur_2(17) >= (orbit size) if Spur counts exponent-set reps; >= (#orbits) if it counts")
print("   rotation classes. Both are honest LOWER bounds; the shipped thm gives the >=1 floor.")
