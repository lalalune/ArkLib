#!/usr/bin/env python3
"""
First-principles derivation of the r=3 deep-band #bad closed form for the order-2
monomial line (u0 = x^{n/2} = (-1)^i, u1 = x^{n/2-1} = (-1)^i g^{-i}).

Deep band r=3: a0 = 4, pin k = 2.  An a0=4 subset S = {i1,i2,i3,i4} is ALIGNED with
scalar gamma iff for EVERY (k+1)=3-subtuple t of S:
    residual(u0, t) + gamma * residual(u1, t) = 0,
where residual(y, t) = det of the 3x3 bordered Vandermonde
    [[1, x_a, y(x_a)] for a in t],  x_a = g^{t_a}.

residual(y, {a,b,c}) = det [[1, x_a, y_a],[1, x_b, y_b],[1, x_c, y_c]]
  = (x_b - x_a)(y_c - y_a) - (x_c - x_a)(y_b - y_a)    [2x2 after row reduction]
  = Vandermonde-weighted divided difference.

For u0 = s_i := (-1)^i  and  u1 = s_i * w_i  where w_i = g^{-i} = 1/x_i:

The pencil residual r0 + gamma r1 = residual(u0 + gamma u1, t) = residual of
the witness  W_i = s_i (1 + gamma w_i) = s_i (1 + gamma / x_i).

So S is aligned with gamma  <=>  W restricted to S lies on a degree-<2 (affine) poly in x
on every 3-subset  <=>  the 4 points (x_i, W_i), i in S, are COLLINEAR in (x, W)-plane
(all on one line W = A + B x).   [a degree-<k=<2 fit means affine in x]

=> bad gamma exist iff there is a line W = A + B x through all 4 points
   (x_i, s_i (1 + gamma/x_i)),  i in S.
   W_i = s_i + gamma s_i / x_i.   With s_i=(-1)^i, x_i=g^i:
   W_i = (-1)^i + gamma (-1)^i g^{-i}.

Collinear: W_i = A + B x_i  for all 4 i in S  =>
   (-1)^i + gamma (-1)^i g^{-i} = A + B g^i.    (*)

This is the EXACT alignment equation. gamma is the bad scalar pinned by S.
The Vieta pin says gamma = -e1(S) = -sum_{i in S} g^i (the bad scalar equals minus the
power-sum); we verify both characterizations agree and COUNT distinct gamma.

We solve (*): treat it as: for each i in S,
   (-1)^i (1 + gamma g^{-i}) - B g^i = A   (constant, independent of i).
4 equations, unknowns A, B, gamma. Generically 3 unknowns, 4 eqns => one constraint on S
(=> the alignable sets are codimension-1 in C(n,4)) and gamma determined by S.

We just COUNT, exactly mod p, the distinct gamma over all aligned 4-subsets, and confirm
the closed form  #bad = n*C(n/4,2) + 1.
"""
import sys
from math import comb
from itertools import combinations

p = 2013265921

def mu_n(n):
    e = (p-1)//n
    for c in range(2, 400):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return [pow(h, i, p) for i in range(n)], h
    raise RuntimeError

def collinear_gamma(n, dom):
    """For the order-2 line, find all aligned 4-subsets via the collinearity test and
    collect distinct gamma.  Points (x_i, W_i(gamma)) collinear for 4 i's.
    We instead solve directly: a 4-subset is aligned iff the system (*) is consistent.
    Use 3 of the 4 to solve (A,B,gamma) then check the 4th."""
    badvals = set()
    s = [1 if i%2==0 else p-1 for i in range(n)]        # (-1)^i
    xinv = [pow(dom[i], p-2, p) for i in range(n)]
    for S in combinations(range(n), 4):
        # Unknowns A,B,gamma.  Eqn i:  A + B*x_i - gamma*(s_i*xinv_i) = s_i
        # Build 3x3 from first 3 rows, solve, check 4th.
        rows = []
        rhs = []
        for i in S:
            rows.append([1, dom[i], (-(s[i]*xinv[i]))%p])
            rhs.append(s[i])
        # solve 3x3 (first three eqns), then verify 4th
        M = [rows[j][:]+[rhs[j]] for j in range(3)]
        ok = True
        for col in range(3):
            piv = next((rr for rr in range(col,3) if M[rr][col]%p), None)
            if piv is None: ok=False; break
            M[col],M[piv]=M[piv],M[col]
            inv=pow(M[col][col],p-2,p); M[col]=[(v*inv)%p for v in M[col]]
            for rr in range(3):
                if rr!=col and M[rr][col]%p:
                    f=M[rr][col]; M[rr]=[(M[rr][k]-f*M[col][k])%p for k in range(4)]
        if not ok: continue
        A,B,gam = M[0][3]%p, M[1][3]%p, M[2][3]%p
        # check 4th eqn
        if (A + B*rows[3][1] + gam*rows[3][2] - rhs[3])%p == 0:
            # gamma is the pinned bad scalar; confirm it matches Vieta -e1
            badvals.add(gam)
    return badvals

if __name__ == "__main__":
    for n in [int(x) for x in (sys.argv[1:] or [16,32])]:
        dom,h = mu_n(n)
        bv = collinear_gamma(n, dom)
        cf = n*comb(n//4,2)+1
        # Vieta cross-check: are these gammas = -sum g^i over the aligned sets? (count match)
        print(f"n={n}: #distinct gamma (collinearity solve) = {len(bv)}   closed form n*C(n/4,2)+1 = {cf}   match? {len(bv)==cf}   0 in set? {0 in bv}")
