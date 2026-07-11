"""
Probe: does the Spur (spurious char-p collision) tower have a clean DECIDABLE weight-4 witness,
analogous to the weight-3 m=3 witness (1+X+X^3 shares X^2+X-1 with Phi_8 over F_3)?

We test, over F_p[X], whether Phi_{2^m}(X) and a candidate antipodal-free relation polynomial
R_T(X) = sum_{i in T} X^i (with T antipodal-free: no two indices differ by 2^{m-1})
are NON-COPRIME (share a non-unit factor) <=> p | N(sigma_T) <=> exists primitive 2^m-th root g
in Fbar_p with R_T(g)=0.

This is the resultant-free / norm-free decidable characterization used in SpurWeightThreeCollision.
We look for the SMALLEST odd prime p and a weight-4 antipodal-free T at m=4 (mu_16) giving a
collision, to confirm the tower extends to weight 4 with a concrete, formalizable witness.
"""
import sympy as sp
from sympy import Poly, symbols, GF, gcd, cyclotomic_poly, factorint, isprime

X = symbols('X')

def antipodal_free(T, m):
    half = 1 << (m - 1)
    s = set(T)
    for i in T:
        if (i + half) % (1 << m) in s:
            return False
    return True

def rel_poly(T):
    e = 0
    for i in T:
        e += X**i
    return Poly(e, X)

def collides(p, m, T):
    """True if Phi_{2^m} and R_T share a non-unit factor over F_p (=> p | N(sigma_T))."""
    Phi = Poly(cyclotomic_poly(1 << m, X), X, domain=GF(p))
    R = Poly(rel_poly(T).as_expr(), X, domain=GF(p))
    g = Phi.gcd(R)
    return g.degree() >= 1, g

# weight-3 sanity (must reproduce m=3, p=3, T={0,1,3})
ok, g = collides(3, 3, [0,1,3])
print(f"[sanity] m=3 p=3 T=(0,1,3) weight-3 collision: {ok}, shared gcd deg {g.degree()} = {g.as_expr()}")

# weight-4 search at m=4 (mu_16), antipodal-free 4-subsets of {0..15}, smallest odd prime collision
from itertools import combinations
m = 4
found = []
for T in combinations(range(1 << m), 4):
    if 0 not in T:  # WLOG include 0 (rotation), reduces search
        continue
    if not antipodal_free(T, m):
        continue
    # find smallest odd prime p with a collision
    for p in [3,5,7,11,13,17,19,23,29,31,37,41]:
        ok, g = collides(p, m, list(T))
        if ok:
            found.append((T, p, g.degree(), str(g.as_expr())))
            break
    if len(found) >= 8:
        break

print(f"\n[weight-4 collisions at m=4, mu_16] (T, smallest odd prime p, shared-deg, shared factor):")
for (T, p, gd, ge) in found:
    print(f"  T={T}  p={p}  sharedDeg={gd}  factor={ge}")

# also report the explicit norm factorizations for the documented weight-4 reps
print("\n[norm factorizations of documented weight-4 reps]")
for m in [4,5]:
    T = [0,1,2,4]  # 1 + z + z^2 + z^4, antipodal-free for m>=4 (half=8 or 16)
    if antipodal_free(T, m):
        zeta = sp.exp(2*sp.pi*sp.I/(1<<m))
        sigma = sum(zeta**i for i in T)
        mp = sp.Poly(sp.minimal_polynomial(sigma, X), X)
        Nval = int(sp.Abs(mp.eval(0)))
        print(f"  m={m}: N(1+z+z^2+z^4) = {Nval} = {factorint(Nval)}")
