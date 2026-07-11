from sympy import symbols, Poly, Rational, expand
n,t=symbols('n t')
g = 56756700*n**6 - 728377650*n**5 + 5439183750*n**4 - 25055875845*n**3 + 69934975110*n**2 - 107438611995*n + 68492499075
# u = 2n-5  (>=1 when n>=3). n=(u+5)/2. Compute 2^6 * g as polynomial in u with integer nonneg coeffs.
u=symbols('u')
gn = g.subs(n,(u+5)/2)
expr = expand(64*gn)  # 2^6 * g
p=Poly(expr,u)
print("64*g(n) as poly in u=2n-5:")
allnn=True
coeffs={}
for d,c in sorted(p.terms()):
    coeffs[d[0]]=c
    print(f"  u^{d[0]}: {c}  (>=0: {c>=0})")
    if c<0:allnn=False
print("ALL NONNEG:",allnn)
# So 64*g(n) = sum c_k * (2n-5)^k, all c_k>=0 integers. For n>=3, (2n-5)>=1>0 => g>0.
# Verify
for nv in [3,4,8,16]:
    lhs=64*int(g.subs(n,nv))
    uv=2*nv-5
    rhs=sum(int(coeffs.get(k,0))*uv**k for k in range(7))
    print(f"n={nv}: 64g={lhs} cert={rhs} match={lhs==rhs}")
# Also the deficit_factored form: deficit = n*g(n). And we need E8<=wick i.e. deficit>=0.
# print integer coeff list for Lean
print("COEFFS_U:", [int(coeffs.get(k,0)) for k in range(7)])
