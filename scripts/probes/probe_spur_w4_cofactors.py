"""Compute exact cofactors over F_17 for the Lean weight-4 collision file:
  X^8 + 1          = (X - 12) * Q(X)   over F_17
  1 + X + X^2 + X^4 = (X - 12) * R(X)   over F_17
so we can write linear_combination / explicit Dvd witnesses. Use 12 = -5 mod 17."""
import sympy as sp
from sympy import symbols, Poly, GF, div

X = symbols('X')
p = 17
g = 12

Phi16 = Poly(X**8 + 1, X, domain=GF(p))
Rel   = Poly(1 + X + X**2 + X**4, X, domain=GF(p))
lin   = Poly(X - g, X, domain=GF(p))  # = X - 12

Q, rQ = Phi16.div(lin)
R, rR = Rel.div(lin)
print("X^8+1 = (X-12)*Q,  Q =", Q.as_expr(), " remainder:", rQ.as_expr())
print("1+X+X^2+X^4 = (X-12)*R,  R =", R.as_expr(), " remainder:", rR.as_expr())

# Express coefficients as signed residues in [-8,8] for clean Lean literals
def signed(c):
    c = int(c) % p
    return c - p if c > p//2 else c

print("\nQ coeffs (low->high):", [signed(c) for c in reversed(Q.all_coeffs())])
print("R coeffs (low->high):", [signed(c) for c in reversed(R.all_coeffs())])

# Verify the deg-1 root identities mod 17 (for the decide-based Lean proof):
print("\nmod-17 checks:")
print("  g^8 + 1 =", (g**8 + 1) % p)
print("  1 + g + g^2 + g^4 =", (1 + g + g**2 + g**4) % p)
print("  order of g:", end=' ')
o=1; x=g%p
while x!=1: x=x*g%p; o+=1
print(o)
