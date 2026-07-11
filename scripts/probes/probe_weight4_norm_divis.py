#!/usr/bin/env python3
"""
Probe: weight-4 antipodal-free short-relation norms N(sigma_T) over Q(zeta_{2^m}),
and whether an odd prize prime p can divide them.

WEIGHT-2 BASE (landed a823e4658): sigma = 1 - zeta^j (j odd) has N = Phi_{2^m}(1) = 2.
=> odd p never divides => weight-2 Spur = 0.

WEIGHT-4 next rung: sigma = 1 + eps1*zeta^a + eps2*zeta^b + eps3*zeta^c  (eps in {+1,-1}),
antipodal-free (no pair sums to 0, i.e. no two terms are negatives: u_i + u_j != 0).
Antipodal pair = {zeta^i, -zeta^i} = {zeta^i, zeta^{i + 2^{m-1}}}.

We compute N(sigma_T) = prod over primitive 2^m-th roots, = Res(R_T(x), Phi_{2^m}(x)) up to sign,
equivalently |Norm| = abs(resultant). Use sympy over ZZ. The relation polynomial R_T(x) =
sum eps_i x^{e_i}. Norm = product_{zeta primitive} R_T(zeta) = res(Phi, R_T)/lc^... ; use
sympy.resultant.

Question: do any weight-<=4 antipodal-free T give N(sigma_T) with an ODD prime factor?
If yes, that odd prime is a candidate "bad prime" where char-p energy exceeds char-0 at weight 4.
This is the genuine content of the next rung.
"""
import sympy as sp
from sympy import symbols, Poly, cyclotomic_poly, resultant, factorint, ZZ
from itertools import combinations, product

x = symbols('x')

def antipodal_free(exps, signs, N):
    # terms are signs[i] * zeta^{exps[i]}.  antipodal pair: signs[i]*z^{e_i} + signs[j]*z^{e_j} = 0
    # => signs[i]*z^{e_i} = -signs[j]*z^{e_j} => z^{e_i-e_j} = -signs[i]*signs[j]
    # = z^{half} if signs equal, = z^0=1 if signs opposite. z^{e_i-e_j}=1 impossible distinct exps mod N.
    # antipodal <=> e_i - e_j == N//2 (mod N) AND signs equal, OR (e_i==e_j and signs opposite -> not distinct)
    half = N // 2
    for i in range(len(exps)):
        for j in range(i+1, len(exps)):
            d = (exps[i] - exps[j]) % N
            if d == half and signs[i] == signs[j]:
                return False
            if d == 0:
                return False
    return True

def relation_norm(exps, signs, m):
    N = 2**m
    Phi = cyclotomic_poly(N, x)
    R = sum(s * x**e for s, e in zip(signs, exps))
    Rp = Poly(R, x, domain=ZZ)
    Phip = Poly(Phi, x, domain=ZZ)
    res = resultant(Phip, Rp)
    return int(res)

for m in range(2, 6):
    N = 2**m
    print(f"\n===== m={m}, N=2^{m}={N}, phi(N)={N//2} =====")
    odd_factor_seen = []
    # weight-4: 1 (sign +1 fixed at exp 0 by unit normalization) + 3 more terms
    # general: choose 3 distinct nonzero exps, 3 signs; first term 1
    cnt = 0
    norms = {}
    for exps3 in combinations(range(1, N), 3):
        for signs3 in product([1,-1], repeat=3):
            exps = (0,) + exps3
            signs = (1,) + signs3
            if not antipodal_free(exps, signs, N):
                continue
            nv = relation_norm(exps, signs, m)
            cnt += 1
            anv = abs(nv)
            norms[anv] = norms.get(anv, 0) + 1
            if anv == 0:
                continue
            f = factorint(anv)
            odds = [pp for pp in f if pp != 2]
            if odds:
                odd_factor_seen.append((exps, signs, anv, f))
    print(f"  antipodal-free weight-4 relations tested: {cnt}")
    # show norm value histogram (top few)
    items = sorted(norms.items())
    print(f"  distinct |N| values: {len(items)}; smallest few: {items[:8]}")
    if odd_factor_seen:
        print(f"  *** {len(odd_factor_seen)} relations with an ODD prime factor in |N|:")
        for (e,s,anv,f) in odd_factor_seen[:6]:
            print(f"      exps={e} signs={s} |N|={anv} = {f}")
    else:
        print(f"  NO odd prime factor in any weight-4 antipodal-free norm. All |N| are powers of 2 (or 0).")
