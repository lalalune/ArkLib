"""Verify the explicit weight-4 Spur witness at p=17, m=4: g=12 is a primitive 16th root
of unity in F_17, antipodal-free relation 1 + g + g^2 + g^4 = 0 mod 17, which does NOT
hold over C (1+zeta+zeta^2+zeta^4 != 0). Confirms Spur_2(17) >= 1 at weight 4 with a
BASE-FIELD root (deg-1 factor) -- the cleanest possible formalization target."""
p = 17
# candidate root g = -5 mod 17 = 12
g = (-5) % p
print(f"g = {g}")
# order of g in F_17^*
order = 1
x = g % p
while x != 1:
    x = (x * g) % p
    order += 1
print(f"order of g in F_17^* = {order}  (primitive 16th root <=> order == 16)")
# the relation 1 + g + g^2 + g^4 mod 17
val = (1 + g + g**2 + g**4) % p
print(f"1 + g + g^2 + g^4 mod 17 = {val}  (collision <=> 0)")
# is g a root of Phi_16 = X^8 + 1 mod 17?
phi16 = (g**8 + 1) % p
print(f"g^8 + 1 mod 17 = {phi16}  (g is primitive 16th root <=> 0, i.e. g^8 = -1)")
# antipodal-free check: T={0,1,2,4}, half=8, no two indices differ by 8: trivially true (all < 8)
T = [0,1,2,4]; half = 8
af = all(((i+half) % 16) not in set(T) for i in T)
print(f"T={T} antipodal-free (no pair differs by 8): {af}")
# over C, 1+zeta+zeta^2+zeta^4 != 0:
import cmath, math
z = cmath.exp(2j*math.pi/16)
cval = 1 + z + z**2 + z**4
print(f"over C: |1+zeta+zeta^2+zeta^4| = {abs(cval):.6f}  (nonzero => char-p-only relation)")
# all eight primitive 16th roots in F_17 (the deg-1 factors found): list roots of X^8+1
roots = [a for a in range(1,17) if (a**8 + 1) % 17 == 0]
print(f"primitive 16th roots in F_17 (roots of X^8+1): {roots}")
# which of them kill 1+X+X^2+X^4 ?
killers = [a for a in roots if (1 + a + a**2 + a**4) % 17 == 0]
print(f"of those, roots of 1+X+X^2+X^4: {killers}")
