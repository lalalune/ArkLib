#!/usr/bin/env python3
"""Coordinate sensitivity and positive full-kernel acceleration controls.

See docs/kb/astra_acceleration_chart-2026-09-05.md. No prize bound or
production properness claim follows from these finite controls.
"""
from itertools import combinations, product
import json

from astra_acceleration_extension_check import basis, contact, power_mod, linear_combination
from astra_hasse_order_two_check import coefficients, rank_one, dense_rank
from astra_positive_kernel_factor_check import (
    trim, add, mul, scale, divide, gcd, deriv, locator, evaluate, kernel,
)

U1 = (238,84,40,219,30,215,254,215,247)


def derivative(poly, axis, p):
    out = {}
    for mon,c in poly.items():
        if mon[axis]:
            key = list(mon)
            key[axis] -= 1
            value = c*mon[axis] % p
            if value:
                out[tuple(key)] = value
    return out


def specialize(poly, axis, values, p):
    """Leave one variable free and substitute the other coordinates."""
    out = [0]*(1+max(mon[axis] for mon in poly))
    for mon,c in poly.items():
        j = 0
        for i in range(len(mon)):
            if i != axis:
                c = c*pow(values[j],mon[i],p) % p
                j += 1
        out[mon[axis]] = (out[mon[axis]]+c) % p
    return trim(out,p)


def certify_linear_R_irreducible(F,p):
    parts = [{(x,y,z):c for (x,y,r,z),c in F.items() if r == j}
             for j in (0,1)]
    assert len(parts[0])+len(parts[1]) == len(F) and all(parts)
    witnesses = []
    # A common nonconstant factor has positive degree in at least one
    # of X,Y,Z. Degree-preserving coprime specializations exclude each.
    for axis in range(3):
        degrees = [max(mon[axis] for mon in a) for a in parts]
        witness = None
        for values in product(range(1,20),repeat=2):
            unis = [specialize(a,axis,values,p) for a in parts]
            if [len(a)-1 for a in unis] == degrees and gcd(*unis,p) == [1]:
                witness = {"free_axis":axis,"other_values":list(values),
                           "preserved_degrees":degrees}
                break
        assert witness is not None
        witnesses.append(witness)
    return witnesses


def irreducible_six(modulus,p):
    assert len(modulus) == 7 and modulus[-1] == 1
    for e in (2,3):
        difference = add(power_mod([0,1],p**e,modulus,p),[0,-1],p)
        if gcd(modulus,difference,p) != [1]:
            return False
    return power_mod([0,1],p**6,modulus,p) == [0,1]


def generic_acceleration_degree(F,p):
    FX,FY,FR = [derivative(F,j,p) for j in range(3)]
    for x,y,r in product(range(9,25),range(1,12),range(1,12)):
        modulus = specialize(F,3,(x,y,r),p)
        if len(modulus) != 7:
            continue
        modulus = scale(modulus,pow(modulus[-1],-1,p),p)
        if not irreducible_six(modulus,p):
            continue
        numerator = scale(add(specialize(FX,3,(x,y,r),p),
                              scale(specialize(FY,3,(x,y,r),p),r,p),p),-1,p)
        denominator = scale(specialize(FR,3,(x,y,r),p),2,p)
        assert denominator
        inverse = power_mod(denominator,p**6-2,modulus,p)
        assert divide(mul(denominator,inverse,p),modulus,p)[1] == [1]
        acceleration = divide(mul(numerator,inverse,p),modulus,p)[1]
        powers = [power_mod(acceleration,j,modulus,p) for j in range(6)]
        rank = dense_rank([a+[0]*(6-len(a)) for a in powers],p)
        if rank == 6:
            return {"point_X_Y_R":[x,y,r],"monic_Z_modulus":modulus,
                    "acceleration_coordinates":acceleration,"power_rank":rank,
                    "generic_acceleration_degree":6,"generic_relative_degree":1}
    raise AssertionError("No specialization certificate found in the explicit search box")


def positive_full_kernel(p):
    n,w,A,m,D,T,r,s = 9,2,5,3,15,6,1,0
    mons = basis(D,w,T,r,s)
    columns = []
    for mon in mons:
        column = {}
        for node in range(n):
            column.update({(node,)+key:c for key,c in
                           contact(mon,node,int(node>=A),U1[node],m,p,order=1).items()})
        columns.append(column)
    keys = sorted({key for col in columns for key in col})
    matrix = [[col.get(key,0) for col in columns] for key in keys]
    rank,vectors = kernel(matrix,p)
    C = coefficients(D,w,T,r,s)
    L = rank_one(D,w,T,m,r)
    assert C == len(mons) == 532 and L == 59 and C-n*L == 1
    assert rank == 531 and len(vectors) == 1
    F = {(x,y,rr,z):c for (x,y,rr,ss,z),c in zip(mons,vectors[0]) if c}
    assert max(mon[2] for mon in F) == 1
    assert max(mon[3] for mon in F) == 6
    assert max(sum(mon[1:]) for mon in F) == 6
    assert not any(c for (x,y,rr,z),c in F.items() if (y,rr,z) == (0,0,0))
    regular = {x:c for (x,y,rr,z),c in F.items() if (y,rr,z) == (0,1,0)}
    assert regular
    # Every quadratic matching >=3 nodes appears in this enumeration.
    maximum = 0
    for triple in combinations(range(n),3):
        f = []
        for node in triple:
            numerator = locator([x for x in triple if x != node],p)
            scalar = U1[node]*pow(evaluate(numerator,node,p),-1,p) % p
            f = add(f,scale(numerator,scalar,p),p)
        maximum = max(maximum,sum(evaluate(f,x,p) == U1[x] % p for x in range(n)))
    assert maximum == 3 < A
    primitivity = certify_linear_R_irreducible(F,p)
    field = generic_acceleration_degree(F,p)
    return {"prime":p,"columns":C,"single_node_rank":L,"global_rank":rank,
            "uniform_margin":1,"kernel_dimension":1,"nonzero_terms":len(F),
            "irreducibility_certificates":primitivity,"field_certificate":field,
            "maximum_quadratic_agreement_with_u1":maximum,
            "selected_zero_solution_regular":True,
            "production_flag_realized":False}


def jet_matrix_control(p):
    # g=g0+E*(a+bX+cX^2); the Hasse-jet matrix has determinant E^3.
    out = []
    for nodes in ((),(0,),(0,1),(1,3,4)):
        E = locator(nodes,p)
        polys = [[0]*j+E for j in range(3)]
        rows = [polys, [deriv(a,p) for a in polys],
                [scale(deriv(deriv(a,p),p),pow(2,-1,p),p) for a in polys]]
        det = []
        for perm,sign in (((0,1,2),1),((1,2,0),1),((2,0,1),1),
                          ((2,1,0),-1),((1,0,2),-1),((0,2,1),-1)):
            term = [1]
            for row,col in enumerate(perm):
                term = mul(term,rows[row][col],p)
            det = add(det,scale(term,sign,p),p)
        assert det == mul(mul(E,E,p),E,p)
        row = {"nodes":list(nodes),"determinant_degree":len(det)-1}
        if nodes:
            # At z=w-1 the root-count repair inequality can fail by one.
            Ep = deriv(E,p)
            EE = mul(E,E,p)
            J = add(mul(Ep,Ep,p),scale(mul(E,deriv(Ep,p),p),-pow(2,-1,p),p),p)
            assert gcd(EE,J,p) == [1]
            G = {}
            for exponents,coefs in (((0,0,1,0),EE),((0,1,0,0),scale(mul(E,Ep,p),-1,p)),
                                    ((1,0,0,0),J)):
                for x,c in enumerate(coefs):
                    if c:
                        G[(x,)+exponents] = c
            orders = []
            for node in nodes:
                local = linear_combination([(c,contact(mon,node,0,0,4,p))
                                            for mon,c in G.items()],p)
                orders.append(min(mon[0]+3*mon[1] for mon in local))
            w = len(nodes)+1
            weight = max(x+w*y+(w-1)*r+(w-2)*s for x,y,r,s,z in G)
            assert orders == [3]*len(nodes) and weight == 3*len(nodes)-1
            row.update(boundary_contact_sum=sum(orders),boundary_weight=weight)
        out.append(row)
    # At X=0, G=2X^2*S-X*R+Y has contact two for the zero word.
    # For g=X*(a+bX+cX^2), substitution gives bX^2+4cX^3.
    for a,b,c in product(range(3),repeat=3):
        g = [0,a,b,c]
        gp = deriv(g,p)
        gs = scale(deriv(gp,p),pow(2,-1,p),p)
        value = add(add([0,0]+scale(gs,2,p),[0]+scale(gp,-1,p),p),g,p)
        assert value == trim([0,0,b,4*c],p)
    return out


def main():
    controls = [positive_full_kernel(p) for p in (257,65537,2130706433)]
    jets = [{"prime":p,"determinants":jet_matrix_control(p)}
            for p in (17,257,2130706433)]
    n,w = 262144,131071
    assert n//(w-1) == 2
    print(json.dumps({"status":"PASS_ACCELERATION_CHART_CONTROLS",
                      "positive_full_kernels":controls,"generic_jet_controls":jets,
                      "production_maximum_constants_exceeding_zero_allowance":2,
                      "production_properness_proved":False,"prize_bound_improved":False,
                      "independent_review_and_Lean_complete":False},sort_keys=True))


if __name__ == "__main__":
    main()
