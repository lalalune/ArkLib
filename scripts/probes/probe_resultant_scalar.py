# Probe: for the two-pencil Q0 + gamma*Q1 over mu_n, count "bad scalars" gamma
# such that resultant_X( Q0 + gamma Q1, prod_{S}(X-z) ) shares a factor,
# i.e. gamma is a ROOT of Res_X(Q0 + gamma Q1 - W, m_S) viewed as poly in gamma.
# Key lens question: is #{bad gamma} controlled by deg in gamma (= q-independent),
# and does the resultant-as-poly-in-gamma have degree = |S| (the agreement size),
# NOT degree depending on q?  That is the deg-Q1 control residual.
import numpy as np
from numpy.polynomial import polynomial as P
import itertools, math

# Symbolic check over Q[gamma]: Res_X(Q0(X)+gamma*Q1(X) - W(X), prod_{z in S}(X-z))
# = prod_{z in S} (Q0(z)+gamma*Q1(z) - W(z))   (resultant w.r.t. monic m_S = prod(X-z))
# So as a polynomial in gamma it has degree = #{z in S : Q1(z) != 0} <= |S|.
# => #bad gamma (its roots) <= |S| = a, INDEPENDENT of q.  This is exactly survivor-1's
# pinning re-expressed as a resultant. The point of WAVE-2: for a STACK (Q1 a row-vector,
# the pencil agreeing with a CODEWORD W of deg<k means W is free), the resultant identity
# Res_X(.,m_S) = prod_{z in S}(Q0(z)+gamma Q1(z)-W(z)) still holds, and the W-freedom is
# absorbed because W is determined on S by <k points once a>k.  Verify the degree-in-gamma
# claim numerically.
import sympy as sp
g = sp.symbols('gamma')
X = sp.symbols('X')
# random Q0, Q1 over rationals, S of size a
np.random.seed(1)
for trial in range(5):
    a = np.random.randint(3,7)
    Sset = list(range(1,a+1))
    Q0c = [sp.Integer(int(c)) for c in np.random.randint(-3,4,a+2)]
    Q1c = [sp.Integer(int(c)) for c in np.random.randint(-3,4,a+2)]
    Q0 = sum(Q0c[i]*X**i for i in range(len(Q0c)))
    Q1 = sum(Q1c[i]*X**i for i in range(len(Q1c)))
    mS = sp.prod([X - z for z in Sset])
    pen = Q0 + g*Q1
    R = sp.resultant(sp.Poly(pen, X), sp.Poly(mS, X), X)
    R = sp.Poly(sp.expand(R), g)
    deg_g = R.degree()
    nz = sum(1 for z in Sset if sp.simplify(Q1.subs(X,z))!=0)
    print(f"trial {trial}: a={a}, deg_gamma(Res)={deg_g}, #(z in S: Q1(z)!=0)={nz}  match={deg_g==nz}")
print("CONCLUSION: deg_gamma(Res_X(Q0+gamma Q1, m_S)) = #{z in S: Q1(z)!=0} <= a, q-INDEPENDENT.")
