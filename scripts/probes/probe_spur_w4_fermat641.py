"""Weight-4 Spur collision at the STRUCTURED Fermat-type prime 641 (| 2^32+1), m=5 (mu_32).
N(1+z+z^2+z^4) = 2*641 at m=5, so 641 should give a collision. Find the shared-factor degree
(ideally deg-1 base-field root in F_641) and the explicit primitive 32nd root g with
1+g+g^2+g^4 = 0 mod 641. This is the structured-prime rung the brief explicitly wants."""
import sympy as sp
from sympy import symbols, Poly, GF, cyclotomic_poly, factorint

X = symbols('X')
p = 641
m = 5
N = 1 << m  # 32
half = N >> 1  # 16

# sanity: 641 | 2^32 + 1 (Fermat F_5 factor)
print(f"641 | 2^32+1 : {(2**32 + 1) % 641 == 0}")
print(f"(p-1) % N = {(p-1) % N}  (need 0 so mu_32 subset F_641^*)")

T = [0,1,2,4]
# antipodal-free at m=5 (half=16)
af = all(((i+half) % N) not in set(T) for i in T)
print(f"T={T} antipodal-free (no pair differs by {half}): {af}")

Phi = Poly(cyclotomic_poly(N, X), X, domain=GF(p))   # = X^16 + 1
R   = Poly(1 + X + X**2 + X**4, X, domain=GF(p))
g = Phi.gcd(R)
print(f"Phi_32 = X^16+1 over F_641; gcd(Phi_32, 1+X+X^2+X^4) degree = {g.degree()}")
print(f"shared factor = {g.as_expr()}")

# if deg 1, extract the base-field root and verify order 32
if g.degree() == 1:
    # factor = X - root  (monic); root = -constant coeff
    cs = g.all_coeffs()
    root = (-int(cs[-1]) * pow(int(cs[0]), -1, p)) % p
    print(f"base-field root g0 = {root}")
    # order
    o=1; x=root%p
    while x!=1: x=x*root%p; o+=1
    print(f"order of g0 = {o} (primitive 32nd root <=> 32)")
    print(f"g0^16 + 1 mod 641 = {(pow(root,16,p)+1)%p}")
    print(f"1+g0+g0^2+g0^4 mod 641 = {(1+root+pow(root,2,p)+pow(root,4,p))%p}")
    # cofactors for Lean
    Q,rQ = Phi.div(Poly(X-root, X, domain=GF(p)))
    Rr,rR = R.div(Poly(X-root, X, domain=GF(p)))
    print(f"X^16+1 = (X-{root})*Q rem {rQ.as_expr()}")
    print(f"1+X+X^2+X^4 = (X-{root})*R rem {rR.as_expr()}")
else:
    # list all base-field roots of each, find common
    rootsPhi = [a for a in range(1,p) if (pow(a,16,p)+1)%p==0]
    rootsR = [a for a in range(1,p) if (1+a+pow(a,2,p)+pow(a,4,p))%p==0]
    common = sorted(set(rootsPhi) & set(rootsR))
    print(f"base-field roots of Phi_32: {len(rootsPhi)}; of relation: {rootsR}; common: {common}")
