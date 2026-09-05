#!/usr/bin/env python3
"""Exact controls for the fixed regularity cube in contact tails.

No improved prize bound. See docs/kb/astra_tail_regularity_cube-2026-09-05.md.
"""
import json

from astra_positive_kernel_factor_check import (
    add as uadd, mul as umul, scale as uscale, divide, gcd, deriv,
)
from astra_acceleration_extension_check import power_mod
from astra_c2_budget_obstruction import mixed, add as flag_add, scale as flag_scale


def add(p, *polys):
    out = {}
    for poly in polys:
        for key,c in poly.items():
            out[key] = (out.get(key,0)+c) % p
    return {key:c for key,c in out.items() if c}


def scale(p, poly, c):
    return {key:a*c % p for key,a in poly.items() if a*c % p}


def mul(p, *polys):
    out = {(0,0,0,0):1}
    for poly in polys:
        result = {}
        for a,ca in out.items():
            for b,cb in poly.items():
                key = tuple(x+y for x,y in zip(a,b))
                result[key] = (result.get(key,0)+ca*cb) % p
        out = {key:c for key,c in result.items() if c}
    return out


def diff(p, poly, axis):
    out = {}
    for key,c in poly.items():
        if key[axis] and c*key[axis] % p:
            new = list(key)
            new[axis] -= 1
            out[tuple(new)] = c*key[axis] % p
    return out


def coefficient(poly, axis, degree):
    return {tuple(0 if j == axis else key[j] for j in range(4)):c
            for key,c in poly.items() if key[axis] == degree}


def evaluate(p, poly, values):
    out = 0
    for key,c in poly.items():
        for d,x in zip(key,values):
            c = c*pow(x,d,p) % p
        out = (out+c) % p
    return out


def surface(r,y,t):
    # F=R+R^r+XY+Y^y+Z^t, with f=0,gamma=0 a regular solution.
    return {(0,0,1,0):1,(0,0,r,0):1,(1,1,0,0):1,
            (0,y,0,0):1,(0,0,0,t):1}


def sparse_controls(p,r,y,t,maximum):
    F = surface(r,y,t)
    R,Y = {(0,0,1,0):1},{(0,1,0,0):1}
    H = diff(p,F,2)
    G = scale(p,add(p,diff(p,F,0),mul(p,R,diff(p,F,1))),-1)
    HX,HY,HR = [diff(p,H,j) for j in range(3)]
    H3 = mul(p,H,H,H)
    def vector(P):
        return add(p,mul(p,H,diff(p,P,0)),mul(p,R,H,diff(p,P,1)),
                   mul(p,G,diff(p,P,2)))
    VH = vector(H)
    def original_step(P,d):
        # Direct transcription of clearedStep in the pinned companion.
        return add(p,mul(p,H,H,diff(p,P,0)),mul(p,R,H,H,diff(p,P,1)),
                   mul(p,G,H,diff(p,P,2)),
                   scale(p,mul(p,P,add(p,mul(p,H,HX),mul(p,R,H,HY),
                                        mul(p,G,HR))),-2*d))
    N = Y
    reduced = Y
    M = None
    nondivisible = None
    counts = []
    for d in range(maximum):
        N = original_step(N,d)
        if d == 1:
            M = G
        elif d >= 2:
            M = add(p,mul(p,H,vector(M)),scale(p,mul(p,M,VH),-(2*d-3)))
        A = coefficient(F,2,r)
        B = coefficient(reduced,2,2*d*(r-1))
        excess = scale(p,add(p,scale(p,mul(p,A,diff(p,B,1)),r),
                              scale(p,mul(p,diff(p,A,1),B),-2*d*r)),r)
        correction = mul(p,excess,{(0,0,(2*d+1)*(r-1),0):1},F)
        reduced = add(p,original_step(reduced,d),scale(p,correction,-1))
        assert max(key[2] for key in reduced) <= 2*(d+1)*(r-1)
        if d >= 1:
            assert N == mul(p,H3,M)
            index = d+1
            assert max(key[2] for key in M) <= (2*r-1)*index-3*r+3
            assert max(key[1]+key[2] for key in M) <= (2*index-3)*(y-1)+1
            assert max(sum(key[1:]) for key in M) <= (2*index-3)*(t-1)+1
            counts.append({"d":d+1,"raw_terms":len(N),"primitive_terms":len(M)})
            if r == 2 and nondivisible is None:
                root = -pow(2,-1,p) % p
                values = (0,1,root,0)
                value = evaluate(p,reduced,values)
                if value:
                    assert evaluate(p,H,values) == 0
                    nondivisible = {"d":d+1,"point":list(values),"value":value}
    if r == 2:
        assert nondivisible is not None
    return {"prime":p,"r":r,"y":y,"t":t,"identities":counts,
            "reduced_representative_not_divisible_by_H":nondivisible}


def exact_order_control(p,r,y,indices):
    # On F=0 specialize Y=1,Z=0, so X=-R-R^r-1. This is regular
    # as a coordinate substitution even at H=0.
    H = [1]+[0]*(r-2)+[r]
    HR = deriv(H,p)
    G = uadd([-1,1-y,1],[0]*(r+1)+[1],p)
    G = divide(G,H,p)[1]
    assert gcd(H,HR,p) == [1]
    assert gcd(H,G,p) == [1]
    scalar = 1
    rows = []
    for d in range(2,max(indices)+1):
        if d > 2:
            scalar = -scalar*(2*d-5) % p
        if d in indices:
            rem = divide(umul(power_mod(G,d-1,H,p),power_mod(HR,d-2,H,p),p),H,p)[1]
            rem = uscale(rem,scalar,p)
            assert rem and gcd(rem,H,p) == [1]
            rows.append({"d":d,"odd_double_factorial_signed":scalar,
                         "primitive_tail_mod_H":rem,"coprime_to_H":True})
    return {"prime":p,"r":r,"y":y,"H_squarefree":True,"rows":rows}


def bookkeeping():
    w = 131071
    F = (2317,37,10)
    H = (2317,37,9)
    tail = (2*2317*(w+1),1+2*37*(w+1),18*(w+1))
    rational = flag_add((4634,74,19),flag_scale(w+1,(2317,36,8)))
    fiber = (2317,37,11)
    cut = flag_add((4634,74,19),flag_scale(w+1,F))
    original = mixed(F,tail,rational)+(w+5)*mixed(F,fiber,cut)
    d = w+1
    primitive = ((2*d-3)*F[0],(2*d-3)*F[1]-d+1,
                 (2*F[2]-1)*d-3*F[2]+3)
    first_old = mixed(F,tail,rational)
    first_primitive = mixed(F,primitive,rational)
    assert primitive == (607380697,9568146,2490341)
    assert first_primitive-first_old == 2926707573042415 > 0
    # An arithmetic grant, not a justified new geometric bound: allow
    # the maximum H flag to be subtracted three times from both cuts.
    shifted_tail = tuple(a-3*b for a,b in zip(tail,H))
    shifted_cut = tuple(a-3*b for a,b in zip(cut,H))
    granted = mixed(F,shifted_tail,rational)+(w+5)*mixed(F,fiber,shifted_cut)
    tail_saving = 3*mixed(F,H,rational)
    moving_saving = 3*(w+5)*mixed(F,fiber,H)
    assert original == 283403712362442072
    assert tail_saving == 2041571922705 and moving_saving == 2315973717288
    assert original-granted == tail_saving+moving_saving == 4357545639993
    target = 266264875801744582
    assert granted > target
    return {"existing_singleton":original,"granted_tail_saving":tail_saving,
            "granted_moving_saving":moving_saving,"total_granted_saving":original-granted,
            "remaining_excess_after_grant":granted-target,
            "primitive_first_tail_flag":primitive,
            "primitive_first_rational_cost":first_primitive,
            "primitive_replacement_increase":first_primitive-first_old,
            "simultaneous_flag_subtraction_proved":False}


def main():
    small = [sparse_controls(p,2,3,4,7) for p in (17,257,2130706433)]
    binding = sparse_controls(2130706433,10,47,2364,4)
    orders = [exact_order_control(p,2,3,[2,3,7]) for p in (17,257)]
    orders.append(exact_order_control(2130706433,10,47,[2,3,131072,131073]))
    print(json.dumps({"status":"PASS_TAIL_REGULARITY_CUBE_CONTROLS",
                      "sparse_controls":small,"binding_sparse_control":binding,
                      "exact_order_controls":orders,"arithmetic_grant":bookkeeping(),
                      "independent_review_and_Lean_complete":False,
                      "full_kernel_provenance_for_binding_example":False,
                      "prize_bound_improved":False},sort_keys=True))


if __name__ == "__main__":
    main()
