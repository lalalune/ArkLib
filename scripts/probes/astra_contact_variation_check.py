#!/usr/bin/env python3
"""Full-kernel MCA witnesses with simple tail intersections.

Exact finite controls for astra_contact_variation-2026-09-05.md.
The examples have R degree one, not the binding C2 degree flag. No prize claim.
"""
import json
from itertools import product
from math import factorial

from astra_colon_audit import direct_contact_matrix, matrix_rank
from astra_far_word_kernel_check import add, derivative, evaluate, mul, scale


def clean(poly):
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def equal(a, b):
    return clean(a) == clean(b)


def sub(a, b, p):
    return add(a, scale(b, -1, p), p)


def power(poly, exponent, p):
    result = [1]
    for _ in range(exponent):
        result = mul(result, poly, p)
    return result


def root_product(nodes, p):
    result = [1]
    for x in nodes:
        result = mul(result, [-x % p, 1], p)
    return result


def divide_linear(poly, root, p):
    # Independent exact synthetic division; returns quotient and remainder.
    work = clean(poly)
    quotient = [0] * (len(work) - 1)
    for j in range(len(work) - 1, 0, -1):
        quotient[j - 1] = work[j]
        work[j - 1] = (work[j - 1] + root * work[j]) % p
    return quotient, work[0]


def control(n, errors, w, p=17):
    nodes = tuple(range(n))
    agreement_nodes = nodes[:n-errors]
    error_nodes = nodes[n-errors:]
    A, pole = n-errors, p-1
    assert n < p and 1 <= errors and 1 <= w <= A-3
    assert n+errors+w+1 <= 2*A
    E, W, L = root_product(error_nodes, p), root_product(agreement_nodes, p), [-pole % p, 1]
    Wp = derivative(W, p)
    # F = AY*Y + H*R + CZ*Z; Q = E^2*F spans the full source kernel.
    AY, H, CZ = sub(W, mul(L, Wp, p), p), mul(L, W, p), Wp
    E2 = mul(E, E, p)
    qY, qR, qZ = (mul(E2, term, p) for term in (AY, H, CZ))
    u0 = (0,)*A + tuple(range(1, errors+1))
    u1 = tuple(pow((x-pole) % p, -1, p) for x in nodes)
    D = n+errors+w+1

    columns, matrix = direct_contact_matrix(
        p, D, 1, 1, 1, nodes, (2,)*n, u0, u1, w)
    rank = matrix_rank(matrix, p)
    assert columns-rank == 1
    basis = [(x, i, j, z) for i in range(2) for j in range(2-i)
             for z in range(2-i-j) for x in range(max(0, D-w*i-(w-1)*j))]
    polys = {(1, 0, 0): qY, (0, 1, 0): qR, (0, 0, 1): qZ}
    vector = [polys.get((i,j,z), [])[x] if x < len(polys.get((i,j,z), [])) else 0
              for x,i,j,z in basis]
    assert len(vector) == columns and any(vector)
    assert all(sum(a*b for a,b in zip(row,vector)) % p == 0 for row in matrix)
    assert len(clean(qY))-1+w < D and len(clean(qR))-1+w-1 < D
    assert len(clean(qZ))-1 < D

    # Independently check the six low-weight coefficients of the substituted Q.
    for i,x in enumerate(nodes):
        ay, hh, cz = (evaluate(poly, x, p) for poly in (qY,qR,qZ))
        ay1, hh1, cz1 = (evaluate(derivative(poly,p),x,p) for poly in (qY,qR,qZ))
        assert all(v % p == 0 for v in
                   (ay*u0[i], ay*u1[i]+cz, hh,
                    ay1*u0[i], ay1*u1[i]+cz1, ay+hh1))
        if i < A:
            # The v coefficient is nonzero, so contact is exactly two.
            assert evaluate(AY,x,p) != 0
            assert evaluate(E,x,p) != 0
        else:
            # E^2 has exact order two and F has a nonzero constant R coefficient.
            assert evaluate(H,x,p) != 0

    # Complete scalar decoding census for every line parameter.
    code = [(coeffs, tuple(evaluate(coeffs,x,p) for x in nodes))
            for coeffs in product(range(p), repeat=w+1)]
    selected = {}
    max_u1_on_agreements = 0
    for coeffs, word in code:
        max_u1_on_agreements = max(max_u1_on_agreements,
            sum(word[i] == u1[i] for i in range(A)))
        for gamma in range(p):
            if sum(word[i] == (u0[i]+gamma*u1[i]) % p for i in range(n)) >= A:
                selected.setdefault(gamma, []).append(coeffs)
    assert selected == {0: [(0,)*(w+1)]}
    assert max_u1_on_agreements == w+1 < A
    quotient_rank = matrix_rank(
        [[pow(x,j,p) for j in range(w+1)]+[u0[i],u1[i]] for i,x in enumerate(nodes)], p)
    assert quotient_rank == w+3

    # Direct surface derivation: D(Y)=(-AY*Y-CZ*Z)/H, D(Z)=0.
    # D^j(Y)=(U_j*Y+V_j*Z)/H^j. No point evaluation substitutes for identities.
    U, V = [1], []
    tails = []
    Hp = derivative(H,p)
    P, remainder = divide_linear(W,pole,p)
    assert remainder == evaluate(W,pole,p) != 0
    Pd = P
    for j in range(w+3):
        if j:
            Pd = derivative(Pd,p)
        signfact = (-1)**j * factorial(j) % p
        Hj = power(H,j,p)
        Lj = power(L,j,p)
        assert equal(mul(add(U,mul(L,V,p),p),Lj,p), scale(Hj,signfact,p))
        assert equal(mul(mul(U,W,p),Lj,p),
                     mul(Hj,add(mul(power(L,j+1,p),Pd,p),[remainder*signfact % p],p),p))
        if j in (w+1,w+2):
            tails.append((U,V))
        nextU = sub(sub(mul(H,derivative(U,p),p),scale(mul(Hp,U,p),j,p),p),mul(AY,U,p),p)
        nextV = sub(sub(mul(H,derivative(V,p),p),scale(mul(Hp,V,p),j,p),p),mul(CZ,U,p),p)
        U,V = nextU,nextV
    determinant = clean(sub(mul(tails[0][0],tails[1][1],p),mul(tails[1][0],tails[0][1],p),p))
    assert determinant
    # The nonzero two-by-two determinant proves a transverse intersection at Y=Z=0.
    # Regularity is generic in X: H is a nonzero polynomial, despite nodewise zeros.
    assert clean(H)

    # Every polynomial infinitesimal deformation solves H*g'+AY*g+CZ*eta=0.
    variation_columns = []
    for j in range(w+1):
        g = [0]*j+[1]
        variation_columns.append(add(mul(H,derivative(g,p),p),mul(AY,g,p),p))
    variation_columns.append(CZ)
    rows = [[col[i] if i < len(col) else 0 for col in variation_columns]
            for i in range(max(map(len,variation_columns)))]
    variation_rank = matrix_rank(rows,p)
    assert variation_rank == w+2
    c = A+w
    guaranteed_good_nodes = 2*A-c+w-1
    assert guaranteed_good_nodes == A-1 > w
    return {"p":p,"n":n,"w":w,"errors":errors,"agreements":A,"source_D":D,
            "source_columns":columns,"source_rank":rank,"source_nullity":1,
            "actual_bad_seeds":list(selected),"selected_polynomial":[0],
            "max_u1_agreement_on_selected_support":max_u1_on_agreements,
            "rank_with_code_and_line_words":quotient_rank,
            "first_two_tail_indices":[w+1,w+2],
            "tail_determinant_degree":len(determinant)-1,
            "tail_determinant_leading_coefficient":determinant[-1],
            "polynomial_variation_rank":variation_rank,
            "factor_R_degree":1}


def integrable_variation_control():
    # A contrasting family has a genuine eta=1 variation and a joint codeword pair.
    p,w,n = 17,2,8
    nodes = tuple(range(n))
    W = root_product(nodes,p)
    Wp = derivative(W,p)
    g = [3,2,1]
    H,J = W,scale(Wp,-1,p)
    K0 = sub(mul(Wp,g,p),mul(W,derivative(g,p),p),p)
    assert equal(add(add(mul(H,derivative(g,p),p),mul(J,g,p),p),K0,p),[])
    for x in nodes:
        value = evaluate(g,x,p)
        assert evaluate(H,x,p) == 0
        assert evaluate(derivative(H,p),x,p) != 0
        assert (evaluate(J,x,p)+evaluate(derivative(H,p),x,p)) % p == 0
        assert (evaluate(J,x,p)*value+evaluate(K0,x,p)) % p == 0
        assert (evaluate(derivative(J,p),x,p)*value+evaluate(derivative(K0,p),x,p)) % p == 0
    columns = [add(mul(H,derivative([0]*j+[1],p),p),mul(J,[0]*j+[1],p),p)
               for j in range(w+1)] + [K0]
    rows = [[col[i] if i < len(col) else 0 for col in columns]
            for i in range(max(map(len,columns)))]
    assert matrix_rank(rows,p) == w+1
    assert all(sum(a*b for a,b in zip(row,g+[1])) % p == 0 for row in rows)
    return {"p":p,"n":n,"w":w,"variation_rank":w+1,"variation_nullity":1,
            "eta_one_variation":g,"all_nodes_good":True,"joint_codeword_pair":True}


def main():
    controls = [control(*case) for case in ((9,1,2),(10,2,2),(8,1,1))]
    print(json.dumps({"status":"PASS_FULL_KERNEL_SIMPLE_TAIL_CONTROLS",
                      "controls":controls,
                      "integrable_variation_control":integrable_variation_control(),
                      "binding_C2_flag_realized":False,
                      "large_selected_family_realized":False,
                      "lean_run_performed":False,
                      "prize_bound_improved":False},indent=2))


if __name__ == "__main__":
    main()
