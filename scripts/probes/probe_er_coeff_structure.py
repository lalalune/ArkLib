from sympy import symbols, factorial2, binomial, Rational, factor, simplify, expand

# Exact E_r closed forms on mu_{2^a} (char-0 faithful), verified:
# E_1 = n
# E_2 = 3n^2 - 3n
# E_3 = 15n^3 - 45n^2 + 40n
# E_4 = 105n^4 - 630n^3 + 1435n^2 - 1155n
# E_5 = 945n^5 - 9450n^4 + 39375n^3 - 77175n^2 + 57456n
n = symbols('n')
E = {
 1: n,
 2: 3*n**2 - 3*n,
 3: 15*n**3 - 45*n**2 + 40*n,
 4: 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n,
 5: 945*n**5 - 9450*n**4 + 39375*n**3 - 77175*n**2 + 57456*n,
}
print("Leading coeff = (2r-1)!!:", {r: factorial2(2*r-1) for r in range(1,6)})
print("\nCoefficient lists (high->low degree, dropping constant 0):")
for r in range(1,6):
    p = E[r].as_poly(n)
    coeffs = p.all_coeffs()
    print(f"E_{r}: {coeffs}")

# Second coefficient c1 (of n^{r-1}) vs leading L=(2r-1)!!.  c1/L:
print("\nsecond coeff / leading:")
for r in range(2,6):
    coeffs = E[r].as_poly(n).all_coeffs()
    L = coeffs[0]; c1 = coeffs[1]
    print(f"r={r}: c1={c1}, L={L}, c1/L={Rational(c1,L)}  (compare -3*C(r,2)={-3*binomial(r,2)})")

# Third coeff?
print("\nthird coeff / leading:")
for r in range(3,6):
    coeffs = E[r].as_poly(n).all_coeffs()
    L=coeffs[0]; c2=coeffs[2]
    print(f"r={r}: c2/L = {Rational(c2,L)}")

# Hypothesis: E_r = (2r-1)!! * n^r * [1 - 3 C(r,2)/n + ... ] ? check exact:
# Actually the recurrence is E_{r+1} = n*E_r + crossMass_r. Let's just verify the
# crossMass closed forms and their EXACT form, which IS provable rung-by-rung.
def cross(r):
    return expand(E[r+1] - n*E[r])
print("\ncrossMass G r = E_{r+1} - n E_r  (exact):")
for r in range(1,5):
    print(f"r={r}: crossMass = {cross(r)}")
    print(f"       step target 2r(2r-1)!! n^{r+1} = {2*r*factorial2(2*r-1)}*n^{r+1}")
    print(f"       factored: {factor(cross(r))}")
