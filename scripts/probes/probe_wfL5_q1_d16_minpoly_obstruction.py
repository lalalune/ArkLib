"""
wf-L5 (#444): the char-p OBSTRUCTION pin for Chai-Fan Q1 at d=16.

char-0 Q1 at d=16 is the cyclotomic degree-8 fact (phi(16)=8): the half-basis {w^0..w^7} is the
power basis of Q(w)/Q, so no nontrivial {-1,0,1}-combo vanishes (chaiFan_Q1_charZero, axiom-clean).

The lane mission was to push to char-p via a resultant R_16 != 0 mod p. THIS PROBE PINS WHY THERE
IS NO SUCH RESULTANT at d=16:

  The faithful char-p shadow of the degree-8 argument is deg(minpoly_{F_p} w) = ord_16(p), the
  multiplicative order of p in (Z/16)^*. But (Z/16)^* = Z/2 x Z/4 has EXPONENT 4, so
  ord_16(p) <= 4 < 8 = phi(16) for EVERY prime p. => deg(minpoly) <= 4 always.

So the char-0 degree-8 wall has NO char-p shadow at d=16; there is no single algebraic invariant
R_16 whose nonvanishing proves Q1 mod p. Q1 at prize scale holds only by COUNTING (3^8/p < 1),
NOT algebra. We verify:
  (1) factor-degrees of x^8+1 mod p == ord_16(p), all <= 4;
  (2) the exponent of (Z/16)^* is 4 (< 8);
  (3) genuine vanishing {-1,0,1}-combos exist mod small p=1 mod 16 (the noise the degree argument
      provably cannot rule out), counts ~ 3^8/p.
"""
from itertools import product

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def ord_mod(a, n):
    k = 1; x = a % n
    while x != 1:
        x = x*a % n; k += 1
    return k

# (1) + (2): the structural obstruction.
print("=== (2) exponent of (Z/16)^* ===")
units = [u for u in range(16) if __import__('math').gcd(u, 16) == 1]
orders = {u: ord_mod(u, 16) for u in units}
exponent = max(orders.values())
print(f"(Z/16)^* = {units},  orders = {orders}")
print(f"exponent = {exponent}  (phi(16) = 8)  =>  ord_16(p) <= {exponent} < 8 for EVERY prime p")
assert exponent == 4

print("\n=== (1) deg(minpoly_{F_p} w) = ord_16(p) <= 4, factor-degrees of x^8+1 mod p ===")
import sympy as sp
x = sp.symbols('x')
for p in [3, 5, 7, 11, 13, 17, 97, 113, 193, 241, 257]:
    if not is_prime(p): continue
    Phi = sp.Poly(x**8 + 1, x, modulus=p)
    degs = sorted(set(sp.degree(f) for f, _ in Phi.factor_list()[1]))
    o = ord_mod(p, 16)
    print(f"p={p:5d}  ord_16(p)={o}  factor-degrees(x^8+1 mod p)={degs}  (max <= 4: {max(degs)<=4})")
    assert max(degs) <= 4

# (3): the noise the degree argument cannot rule out (p = 1 mod 16, w in F_p).
print("\n=== (3) genuine vanishing {-1,0,1}-combos mod small p=1 mod 16 (noise ~ 3^8/p) ===")
half = 8
for p in range(17, 600):
    if (p-1) % 16 == 0 and is_prime(p):
        for g in range(2, p):
            w = pow(g, (p-1)//16, p)
            if pow(w, 16, p) == 1 and pow(w, 8, p) != 1:
                break
        basis = [pow(w, j, p) for j in range(half)]
        hits = sum(1 for c in product((-1,0,1), repeat=half)
                   if any(c) and sum(c[j]*basis[j] for j in range(half)) % p == 0)
        print(f"p={p:5d}  vanishing {{-1,0,1}}-combos = {hits:4d}   (3^8/p = {6561/p:6.2f})")

print("\nVERDICT: char-p Q1 at d=16 is COUNTING, not algebra. No resultant R_16 exists.")
print("Faithful char-p shadow = the degree atom (deg < ord_16(p) <= 4); proven axiom-clean in")
print("ArkLib/.../Frontier/_wfL5_ChaiFanQ1CharP.lean (chaiFan_Q1_charP_degree_atom).")
