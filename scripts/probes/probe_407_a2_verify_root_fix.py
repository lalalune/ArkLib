"""
#407 LANE A2 — corrected verification: p* | Res(Phi_n, R_U) means R_U(zeta)=0 for SOME
primitive n-th root zeta mod p*, not for an arbitrarily chosen g. We must scan all
primitive n-th roots mod p* (the roots of Phi_n mod p*) and confirm at least one gives
a genuine e2=0 (e1^2=p2) with e1 != 0 over Z[zeta].

If a primitive root g' makes e1^2==p2 mod p* AND the same U has e1 != 0 over Z[zeta] AND
R_U != 0 over Z[zeta], then p* is a genuine bad prime = the threshold lower bound.

BUT: the relabeling g -> g' is just a Galois conjugate / relabeling of the SAME mu_n.
So 'a new mod-p* solution exists for U at SOME labeling' is exactly the statement that
matters: the F_p* e2=0 locus (over the canonical mu_n = <g'>) contains U though char-0 does not.
"""
import math
from sympy import symbols, Poly, cyclotomic_poly, ZZ, factorint, resultant, isprime, primitive_root, GF

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

n = 32
Phi = phi(n)
U = (0, 2, 6, 8, 9, 10, 11, 13, 14, 20, 21, 23, 28, 31)
s = Poly(sum(X**i for i in U), X, domain=ZZ)
R = (s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)) % Phi
pstar = 3184895024161
assert isprime(pstar) and (pstar-1) % n == 0

# all primitive n-th roots mod p* = roots of Phi_n over F_p*
g0 = pow(primitive_root(pstar), (pstar-1)//n, pstar)
prim_roots = [pow(g0, j, pstar) for j in range(n) if math.gcd(j, n) == 1]

# e1 and e2-condition evaluated at each primitive root zeta (the labeling mu_n = powers of zeta)
def e1_e2zero_at(zeta):
    # mu_n labeled by zeta: element i is zeta^i. e1 = sum zeta^i, p2 = sum zeta^{2i}
    e1 = sum(pow(zeta, i, pstar) for i in U) % pstar
    p2 = sum(pow(zeta, 2*i, pstar) for i in U) % pstar
    return e1, (e1*e1 - p2) % pstar

found = []
for zeta in prim_roots:
    e1, cond = e1_e2zero_at(zeta)
    if cond == 0 and e1 != 0:
        found.append((zeta, e1))

# char-0: is R_U identically 0 (would mean char-0 solution, not 'new')?
char0_sol = R.is_zero
e1_char0_zero = (Poly(sum(X**i for i in U), X, domain=ZZ) % Phi).is_zero
print(f"=== n=32, U={U}, p*={pstar} (n^{math.log(pstar)/math.log(n):.2f}) ===")
print(f"  char-0: R_U identically 0 over Z[zeta]? {char0_sol}  (False => NOT a char-0 e2=0 solution)")
print(f"  char-0: e1==0 over Z[zeta]? {e1_char0_zero}")
print(f"  # primitive 32nd roots mod p* giving e2=0 & e1!=0 (a NEW mod-p* solution): {len(found)} / {len(prim_roots)}")
if found:
    z,e1 = found[0]
    print(f"  example zeta={z}, e1={e1} -> e1^2 == p2 mod p* (genuine new e2=0 bad scalar at p*)")
    print(f"  ==> CONFIRMED: c(32) >= p* = {pstar} = n^{math.log(pstar)/math.log(n):.2f} >> n^3={n**3}")
else:
    print(f"  p* divides norm but NO labeling gives e2=0?? (would mean spurious / sign issue)")
