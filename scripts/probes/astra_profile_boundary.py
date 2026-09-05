#!/usr/bin/env python3
"""Check the fixed binding-weight window and received-line factor obstruction.

No contact profile, universal factor, or protocol improvement is constructed.
See docs/kb/astra_profile_boundary_2026-09-04.md for the general proofs.
"""
from itertools import product
import json
from math import comb

from astra_companion_parameters import N, W, P, locator_rank
from astra_companion_shared_candidate import coefficients_fast
from astra_incidence_derivative_repair import add, scale, mul, power, diff, variable, contact_order

ONE = {(0,0,0,0):1}
VARIABLES = [variable(i) for i in range(4)]


def substitute(f, replacements):
    result = {}
    for exponent, coefficient in f.items():
        term = scale(ONE,coefficient)
        for replacement, degree in zip(replacements,exponent):
            term = mul(term,power(replacement,degree))
        result = add(result,term)
    return result


def localize(f, x, u0, u1):
    t,v,r,z = VARIABLES
    return substitute(f,[add(t,scale(ONE,x)),
        add(add(scale(ONE,u0),scale(z,u1)),add(mul(r,t),v)),r,z])


def weight(f,w):
    return max(a+w*b+(w-1)*r for a,b,r,z in f)


def invert(f,w,c):
    """X^c F(1/X,X^-w Y,X^(1-w)(wY-XR),Z)."""
    result = {}
    for (a,b,r,z), coefficient in f.items():
        base = c-a-w*b-(w-1)*r
        assert base >= 0
        for j in range(r+1):
            term = {(base+j,b+r-j,j,z):
                coefficient*comb(r,j)*w**(r-j)*(-1)**j % P}
            result = add(result,term)
    return result


def substitution_checks():
    xvar,yvar,rvar,zvar = VARIABLES
    w,d,e = 2,3,1
    u = add(power(xvar,d),mul(zvar,power(xvar,e)))
    slope = diff(u,0)
    checks = 0
    for x in (2,5):
        u0,u1 = pow(x,d,P),pow(x,e,P)
        tx = add(xvar,scale(ONE,-x))
        local_v = add(add(yvar,scale(ONE,-u0)),
                      add(scale(zvar,-u1),scale(mul(rvar,tx),-1)))
        for a,b,r,z in product(range(3),range(3),range(2),range(2)):
            f = mul(mul(power(tx,a),power(local_v,b)),
                    mul(power(rvar,r),power(zvar,z)))
            nu = contact_order(localize(f,x,u0,u1))
            assert nu == a+2*b
            c = weight(f,w)
            ys = max(h+j for _,h,j,_ in f)
            expanded = substitute(f,[xvar,u,add(slope,rvar),zvar])
            shifted = substitute(expanded,[add(xvar,scale(ONE,x)),yvar,rvar,zvar])
            for j in {exponent[2] for exponent in expanded}:
                assert max(exponent[0] for exponent in expanded if exponent[2]==j) <= c+(d-w)*ys-j*(d-1)
            for exponent in shifted:
                assert exponent[1] == 0
                assert exponent[0] >= max(0,nu-exponent[2])
            transformed = invert(f,w,c)
            new_x = pow(x,-1,P)
            assert contact_order(localize(transformed,new_x,
                pow(new_x,w,P)*u0 % P,pow(new_x,w,P)*u1 % P)) == nu
            cnew = weight(transformed,w)
            assert cnew <= c+max(exponent[2] for exponent in f)
            assert cnew >= c  # These test polynomials have no factor X.
            assert invert(transformed,w,cnew) == mul(power(xvar,cnew-c),f)
            checks += 1
    return checks


def main():
    cmin,total,y,r,order = W*47-10,2364,47,10,34
    thresholds = {}
    for repair_r in (9,10):
        target = N*locator_rank(order,total,repair_r)
        base = coefficients_fast(cmin+11,total,repair_r)
        channels = sum(total+1-h-j for j in range(repair_r+1)
                       for h in range(y-j+1))
        # On 10<=delta<W every joint-YR degree<=47 channel is present and
        # degree48 is absent; the count is affine with this exact slope.
        delta = 10+(target-base)//channels+1
        assert 10 < delta < W
        before = coefficients_fast(cmin+delta,total,repair_r)-target
        after = coefficients_fast(cmin+delta+1,total,repair_r)-target
        assert before <= 0 < after and after-before == channels
        for small_delta in range(10):
            assert coefficients_fast(cmin+small_delta+1,total,repair_r) <= target
        thresholds[str(repair_r)] = {"delta":delta,"contact_weight":cmin+delta,
            "nullity_below":before,"nullity_at":after,"affine_slope":channels}
    assert thresholds["9"] == {"delta":42331,"contact_weight":6202658,
        "nullity_below":-865305,"nullity_at":152310,"affine_slope":1017615}
    assert thresholds["10"]["delta"] == 41030
    leading = [(y-j,j,0) for j in range(r+1) if j-r >= 0]
    assert leading == [(37,10,0)]
    positive_nodes = (cmin+1+37-1)//37
    rank33,rank37 = [locator_rank(b,total,9) for b in (33,37)]
    deficit = coefficients_fast(cmin+1,total,9)-N*rank33
    high_nodes = (deficit+rank37-rank33-1)//(rank37-rank33)
    assert (positive_nodes,rank37,rank37-rank33,high_nodes) == (
        166496,13275685,2907900,47572)
    assert (positive_nodes-1)*37 <= cmin < positive_nodes*37
    assert (high_nodes-1)*(rank37-rank33) < deficit <= high_nodes*(rank37-rank33)
    degree_limits = {str(delta):(N*(order-r)-delta-1)//(y-r)
                     for delta in (0,10,42330)}
    assert degree_limits == {"0":170039,"10":170039,"42330":168895}
    for text_delta,limit in degree_limits.items():
        delta = int(text_delta)
        assert (y-r)*limit+delta < N*(order-r)
        assert N*(order-r) <= (y-r)*(limit+1)+delta
        for j in range(r+1):
            upper = cmin+delta+(limit-W)*y-j*(limit-1)
            assert upper < N*(order-j)
    dual_interval = (degree_limits["0"]+1,N+W-degree_limits["10"]-1)
    assert dual_interval == (170040,223175)
    assert W % P != 0
    print(json.dumps({
        "status":"VALID_RECEIVED_LINE_FACTOR_EXCLUSION_NO_GENERAL_BINDING_OR_SCORE_CLOSURE",
        "upstream":"032154395c51fd6f77715a7f42d9a987ab9fb48a",
        "minimum_contact_weight":cmin,
        "exact_minimum_top_YR_monomial_Y_R_X":leading[0],
        "maximum_contact_order_at_exact_minimum":37,
        "minimum_weight_universal_positive_nodes_at_least":positive_nodes,
        "minimum_weight_universal_order_at_least34_nodes":high_nodes,
        "fixed_uniform34_interpolation_thresholds":thresholds,
        "uniform34_not_excluded_by_lowR9_delta_range":[0,42330],
        "received_line_degree_excluded_through":degree_limits,
        "dual_chart_tail_indices_not_excluded":dual_interval,
        "substitution_and_inversion_checks":substitution_checks(),
        "scope":"Uniform order at least34 for factorization; actual excess weight delta; no profile/factor/far-word witness constructed"
    },indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
