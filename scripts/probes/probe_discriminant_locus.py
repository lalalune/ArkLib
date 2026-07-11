# WAVE-2 lever: instead of fixing m_S and asking gamma to make the pencil agree on S,
# count bad gamma via the *discriminant* / *subresultant* of the TWO-pencil with the
# generic degree-<k codeword eliminated. Concretely: the pencil Q0+gamma Q1 agrees with
# SOME deg-<k codeword W on >=a points of mu_n  <=>  the a-th SUBRESULTANT of
# (Q0+gamma Q1) and the vanishing poly Z(X)=X^n-1 (whose roots ARE mu_n) drops rank,
# i.e. gcd_X(Q0+gamma Q1 - W, X^n-1) has degree >= a for some W of deg<k.
# Eliminating W (free, deg<k) the condition is: the (a)x(a) "agreement" structure.
# The lens claim to test: the SET of bad gamma is the zero set of a single resultant/
# discriminant POLYNOMIAL in gamma whose degree depends only on (n,k,a,deg Q1) and NOT q.
#
# Test over actual finite fields F_p with mu_n subgroup: vary p (=q), fixed n,k, random
# stack; count bad gamma directly; check the COUNT is p-independent (the survivor property)
# AND find when it beats the trivial supply C(n,a).
import sympy as sp
from sympy import GF, Poly, gcd, symbols
def mu_n_field(p, n):
    # need n | p-1
    if (p-1) % n: return None
    F = GF(p)
    # find generator of F_p^*
    g = sp.primitive_root(p)
    h = pow(g, (p-1)//n, p)  # element of order n
    return [pow(h, i, p) for i in range(n)]

X = symbols('X')
import random
def count_bad(p, n, k, a, Q0coef, Q1coef):
    mu = mu_n_field(p,n)
    if mu is None: return None
    bad = 0
    for gamma in range(p):
        # pencil values on mu
        vals = []
        for z in mu:
            q0 = sum(Q0coef[i]*pow(z,i,p) for i in range(len(Q0coef)))%p
            q1 = sum(Q1coef[i]*pow(z,i,p) for i in range(len(Q1coef)))%p
            vals.append((z,(q0+gamma*q1)%p))
        # does there exist W deg<k agreeing on >=a of mu?  Interpolate: pick which a points.
        # cheap test: a deg-<k poly is determined by k points; it agrees with pencil on >=a>=k+1
        # iff for SOME a-subset the points lie on a deg<k poly. Equivalent: build the (n)x?
        # Vandermonde and check if pencil-vector is within Hamming distance n-a of RS[k].
        # brute for small n: check all a-subsets for collinearity with deg<k.
        from itertools import combinations
        found=False
        pts=vals
        for sub in combinations(range(n), a):
            xs=[pts[i][0] for i in sub]; ys=[pts[i][1] for i in sub]
            # fit deg<k (=k coeffs) through first k points, check rest
            if len(set(xs))<a: continue
            # Lagrange over F_p on first k points
            kk=k
            # solve Vandermonde k x k
            import numpy as np
            M=[[pow(xs[r],c,p) for c in range(kk)] for r in range(kk)]
            try:
                Mi=sp.Matrix(M).inv_mod(p)
            except Exception:
                continue
            coef=(Mi*sp.Matrix(ys[:kk]))%p
            ok=all((sum(int(coef[c])*pow(xs[r],c,p) for c in range(kk))%p)==ys[r] for r in range(a))
            if ok: found=True; break
        if found: bad+=1
    return bad

random.seed(3)
n,k,a=6,2,4
Q0=[random.randint(0,10) for _ in range(4)]
Q1=[random.randint(0,10) for _ in range(4)]
print("n,k,a=",n,k,a,"supply C(n,a)=",sp.binomial(n,a))
for p in [7,13,19,31,37,43,61,67,73,79]:
    if (p-1)%n==0:
        b=count_bad(p,n,k,a,Q0,Q1)
        print(f"  p={p}: #bad gamma = {b}")
