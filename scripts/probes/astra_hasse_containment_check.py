#!/usr/bin/env python3
"""A full second-Hasse kernel can give no extra cut of an old regular factor.

Exact controls for astra_hasse_containment-2026-09-05.md. These are degree-one
sources with nonpositive uniform dimension margins, not production counterexamples.
"""
import json
from math import comb

from astra_colon_audit import direct_contact_matrix, matrix_rank
from astra_contact_variation_check import clean, equal, power, root_product, sub
from astra_far_word_kernel_check import add, derivative, evaluate, mul, scale


def hasse(poly, point, order, prime):
    return sum(value*comb(j,order)*pow(point,j-order,prime)
               for j,value in enumerate(poly) if j >= order) % prime


def linear_matrix(prime, D, w, nodes, u0, u1):
    # Independent columns for 1,Y,R,S,Z; local Y=u0+u1*Z+t*R-t^2*S+v.
    # At contact order three, v first occurs at the excluded weight three.
    basis = [(var,j) for var,weight in enumerate((0,w,w-1,w-2,0))
             for j in range(D-weight)]
    rows = []
    for node,x in enumerate(nodes):
        for channel in range(4):
            for order in range(3):
                row = []
                for var,j in basis:
                    def coefficient(k):
                        return comb(j,k)*pow(x,j-k,prime) % prime if 0 <= k <= j else 0
                    value = 0
                    if channel == 0:
                        if var == 0:
                            value = coefficient(order)
                        elif var == 1:
                            value = u0[node]*coefficient(order)
                    elif channel == 1:
                        if var == 4:
                            value = coefficient(order)
                        elif var == 1:
                            value = u1[node]*coefficient(order)
                    elif channel == 2:
                        if var == 2:
                            value = coefficient(order)
                        elif var == 1:
                            value = coefficient(order-1)
                    else:
                        if var == 3:
                            value = coefficient(order)
                        elif var == 1:
                            value = -coefficient(order-2)
                    row.append(value % prime)
                rows.append(row)
    return basis, rows


def control(p, n, w, errors):
    A, pole = n-errors, p-1
    assert 2 <= w and 1 <= errors and w+3*errors <= A and n < p
    nodes = tuple(range(n))
    E, W = root_product(nodes[A:],p), root_product(nodes[:A],p)
    L, Wp = [-pole % p,1], derivative(W,p)
    Wpp, half = derivative(Wp,p), pow(2,-1,p)
    H = mul(L,W,p)
    F = [sub(W,mul(L,Wp,p),p), H, [], Wp]  # Y,R,S,Z coefficients.
    # The ordinary total derivative, with delta(Y)=R and delta(R)=2S.
    LF = [derivative(F[0],p), add(F[0],derivative(F[1],p),p),
          scale(H,2,p), derivative(F[3],p)]
    J = sub(mul(Wp,Wp,p),scale(mul(W,Wpp,p),half,p),p)
    P = [sub(mul(L,J,p),mul(W,Wp,p),p),
         sub(mul(W,W,p),mul(H,Wp,p),p), mul(H,W,p), scale(J,-1,p)]
    for f,lf,polynomial in zip(F,LF,P):
        assert equal(polynomial,sub(scale(mul(W,lf,p),half,p),mul(Wp,f,p),p))
    Q = [[]]+[clean(mul(power(E,3,p),term,p)) for term in P]
    u0 = (0,)*A+tuple(range(1,errors+1))
    u1 = tuple(pow((x-pole)%p,-1,p) for x in nodes)
    D = 2*A+3*errors+w
    assert D <= 3*A
    basis, rows = linear_matrix(p,D,w,nodes,u0,u1)
    vector = [Q[var][j] if j < len(Q[var]) else 0 for var,j in basis]
    assert any(vector) and Q[3]
    assert all(len(poly)-1+weight < D for poly,weight in zip(Q,(0,w,w-1,w-2,0)))
    assert all(sum(a*b for a,b in zip(row,vector)) % p == 0 for row in rows)
    rank = matrix_rank(rows,p)
    assert rank == len(basis)-1
    local_ranks = [matrix_rank(rows[12*i:12*(i+1)],p) for i in range(n)]
    assert set(local_ranks) == {12}

    # A separate coefficient/Hasse calculation checks every local condition.
    for i,x in enumerate(nodes):
        ay,b,c,d = Q[1:]
        for order in range(3):
            vals = [hasse(poly,x,order,p) for poly in (ay,b,c,d)]
            previous_a = hasse(ay,x,order-1,p) if order >= 1 else 0
            previous2_a = hasse(ay,x,order-2,p) if order >= 2 else 0
            assert all(v % p == 0 for v in
                       (u0[i]*vals[0],vals[3]+u1[i]*vals[0],
                        vals[1]+previous_a,vals[2]-previous2_a))
        if i < A:
            assert evaluate(Q[1],x,p) != 0  # v coefficient: contact exactly three.
        else:
            assert evaluate(P[2],x,p) != 0  # E^3 supplies exactly three.

    # Verify the cleared pullback is a multiple of F, coefficient by coefficient.
    # G=-(F_X+R F_Y). Hence (2H)P(Y,R,G/(2H),Z)=-2H W' F.
    for index in (0,1,3):
        lhs = sub(scale(mul(H,P[index],p),2,p),mul(P[2],LF[index],p),p)
        rhs = scale(mul(mul(H,Wp,p),F[index],p),-2,p)
        assert equal(lhs,rhs)

    # Add W^2*Z^d to F, for any d>=2. Check the only added coefficient.
    # The same P is a differential consequence despite its smaller Z degree.
    V = mul(W,W,p)
    Vp = derivative(V,p)
    assert equal(scale(mul(W,Vp,p),half,p),mul(Wp,V,p))
    assert equal(mul(P[2],Vp,p),scale(mul(mul(H,Wp,p),V,p),2,p))

    # The older first-order source at the same m=3,D,T=1 is actually empty.
    old_columns, old_matrix = direct_contact_matrix(
        p,D,1,1,1,nodes,(3,)*n,u0,u1,w)
    assert matrix_rank(old_matrix,p) == old_columns
    # Recheck the original m=2 full kernel that supplied the factor F.
    first_D = A+2*errors+w+1
    first_columns, first_matrix = direct_contact_matrix(
        p,first_D,1,1,1,nodes,(2,)*n,u0,u1,w)
    assert first_columns-matrix_rank(first_matrix,p) == 1
    quotient_rank = matrix_rank(
        [[pow(x,j,p) for j in range(w+1)]+[u0[i],u1[i]] for i,x in enumerate(nodes)],p)
    assert quotient_rank == w+3
    margin = len(basis)-sum(local_ranks)
    assert margin == -2*A+3*errors+2*w+3 <= 0
    return {"p":p,"n":n,"w":w,"errors":errors,"agreements":A,
            "second_source_D":D,"second_source_columns":len(basis),
            "second_source_rank":rank,"second_source_nullity":1,
            "uniform_dimension_margin":margin,
            "matching_first_order_columns":old_columns,"matching_first_order_nullity":0,
            "original_first_order_D":first_D,"original_first_order_nullity":1,
            "full_second_kernel_pullback_zero_mod_F":True,
            "added_high_Z_coefficient_identities":True,
            "line_independent_mod_code":True}


def main():
    cases = [(17,9,2,1),(17,6,2,1),(17,10,2,2),(19,11,3,2),
             (257,9,2,1),(65537,9,2,1),(2130706433,9,2,1)]
    print(json.dumps({"status":"PASS_FULL_SECOND_HASSE_CONTAINMENT_CONTROLS",
        "controls":[control(*case) for case in cases],
        "positive_uniform_dimension_certificate":False,
        "binding_C2_flag_realized":False,"lean_run_performed":False,
        "prize_bound_improved":False},indent=2))


if __name__ == "__main__":
    main()
