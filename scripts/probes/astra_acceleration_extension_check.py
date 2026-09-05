#!/usr/bin/env python3
"""Exact controls for the acceleration-extension properness criterion.

The general argument is written, not Lean-verified. These checks cover
coordinate normalization, finite full kernels, and extension-field ranks;
they do not establish the missing production hypothesis or a prize bound.
"""
from itertools import product
import json
from math import comb

from astra_hasse_order_two_check import coefficients, rank_two, dense_rank
from astra_positive_kernel_factor_check import kernel, divide, mul, add, scale, gcd


def basis(D, w, T, r, s):
    return [(x, y, rr, ss, z)
            for y in range(T+1) for rr in range(min(r, T-y)+1)
            for ss in range(min(s, T-y-rr)+1)
            for z in range(T-y-rr-ss+1)
            for x in range(max(0, D-w*y-(w-1)*rr-(w-2)*ss))]


def contact(mon, node, u0, u1, m, p):
    """Exact truncated expansion; local exponents are (t,v,R,S,Z)."""
    x, y, r, s, z = mon
    terms = {(0,0,0,0,0): u0, (0,0,0,0,1): u1,
             (1,0,1,0,0): 1, (2,0,0,1,0): -1, (0,1,0,0,0): 1}
    power = {(0,0,0,0,0): 1}
    for _ in range(y):
        out = {}
        for a, ca in power.items():
            for b, cb in terms.items():
                key = tuple(i+j for i,j in zip(a,b))
                if key[0]+3*key[1] < m:
                    out[key] = (out.get(key,0)+ca*cb) % p
        power = {a:c for a,c in out.items() if c}
    out = {}
    for j in range(min(x,m-1)+1):
        c = comb(x,j)*pow(node,x-j,p) % p
        for (t,v,rr,ss,zz), a in power.items():
            if t+j+3*v < m:
                key = (t+j,v,rr+r,ss+s,zz+z)
                out[key] = (out.get(key,0)+c*a) % p
    return {a:c for a,c in out.items() if c}


def linear_combination(parts, p):
    out = {}
    for scalar, part in parts:
        for a,c in part.items():
            out[a] = (out.get(a,0)+scalar*c) % p
    return {a:c for a,c in out.items() if c}


def translate(mon, c, p):
    x,y,r,s,z = mon
    return {(x,j,r,s,z+y-j): comb(y,j)*pow(c,y-j,p) % p
            for j in range(y+1) if comb(y,j)*pow(c,y-j,p) % p}


def normalization_checks(p):
    mons = basis(15,2,3,3,2)
    allowed = set(mons)
    old_direction = tuple(range(6))
    c = next(c for c in range(p) if c not in old_direction)
    count = 0
    for mon in mons:
        transformed = translate(mon,c,p)
        assert set(transformed) <= allowed
        inverse = linear_combination([(a,translate(b,-c,p))
                                      for b,a in transformed.items()],p)
        assert inverse == {mon:1}
        for node in range(6):
            u0 = int(node == 5)
            left = contact(mon,node,u0,old_direction[node],3,p)
            right = linear_combination([
                (a,contact(b,node,u0,old_direction[node]-c,3,p))
                for b,a in transformed.items()],p)
            assert left == right
            count += 1
    return count


def power_mod(f, exponent, modulus, p):
    out = [1]
    while exponent:
        if exponent & 1:
            out = divide(mul(out,f,p),modulus,p)[1]
        f = divide(mul(f,f,p),modulus,p)[1]
        exponent //= 2
    return out


def irreducible_power_two(modulus, p):
    """Rabin's criterion for a monic polynomial of degree 4 or 8."""
    d = len(modulus)-1
    assert d in (4,8) and modulus[-1] == 1
    x = [0,1]
    half = add(power_mod(x,p**(d//2),modulus,p),[0,-1],p)
    return gcd(modulus,half,p) == [1] and power_mod(x,p**d,modulus,p) == x


def extension_control(p, quadratic):
    # F=R-Y*Z^4 (rational acceleration) or R-Y*Z^4-Z^8
    # (quadratic acceleration). Specialize Y,R only for this finite check.
    found = None
    for y,r in product(range(1,min(p,17)),repeat=2):
        modulus = ([-r]+[0]*3+[y]+[0]*3+[1] if quadratic
                   else [-r*pow(y,-1,p) % p]+[0]*3+[1])
        modulus = [c % p for c in modulus]
        if irreducible_power_two(modulus,p):
            found = y,r,modulus
            break
    assert found is not None
    y,r,modulus = found
    d = len(modulus)-1
    accel = [0]*4+[r*pow(2,-1,p) % p]
    accel = divide(accel,modulus,p)[1]
    accel_powers = [power_mod(accel,k,modulus,p) for k in range(3)]
    vectors = []
    for z in range(4):
        for k in range(3):
            vector = divide([0]*z+accel_powers[k],modulus,p)[1]
            vectors.append(vector+[0]*(d-len(vector)))
    rank = dense_rank(vectors,p)
    assert rank == (8 if quadratic else 4)
    if quadratic:
        # 4S^2+2YR*S-R^3 is the minimal acceleration polynomial.
        relation = add(scale(accel_powers[2],4,p),
                       add(scale(accel,2*y*r,p),[-r**3],p),p)
        assert not relation
        assert len(accel) > 1
        # At the excluded boundary deg_Z=4, R*Z^4-2S vanishes,
        # though its S degree is below the minimal polynomial's degree.
        assert not add([0]*4+[r],scale(accel,-2,p),p)
    else:
        assert accel == [r*r*pow(2*y,-1,p) % p]
    return {"quadratic_acceleration":quadratic,"Y":y,"R":r,
            "Z_extension_degree":d,"acceleration_degree":2 if quadratic else 1,
            "relative_degree":4,"cap_Z":3,"cap_S":2,
            "evaluation_columns":12,"evaluation_rank":rank}


def full_kernel_control(p):
    n,w,A,m,D,T,r,s = 6,2,5,3,15,3,3,2
    mons = basis(D,w,T,r,s)
    columns = []
    for mon in mons:
        out = {}
        for node in range(n):
            out.update({(node,)+a:c for a,c in
                        contact(mon,node,int(node == 5),pow(node+1,-1,p),m,p).items()})
        columns.append(out)
    keys = sorted({a for col in columns for a in col})
    matrix = [[col.get(a,0) for col in columns] for a in keys]
    rank, vectors = kernel(matrix,p)
    C = coefficients(D,w,T,r,s)
    L = rank_two(D,w,T,m,r,s,p)
    assert len(mons) == C and C-n*L > 0 and len(vectors) == C-rank
    witnesses = []
    for quadratic in (False,True):
        witness = None
        # Exact nonvanishing at a regular F point certifies a proper pullback.
        for x,y,z in product((6,7,8),(1,2,3),(1,2,3)):
            rr = (y*pow(z,4,p)+(pow(z,8,p) if quadratic else 0)) % p
            ss = rr*pow(z,4,p)*pow(2,-1,p) % p
            if quadratic:
                assert (4*ss*ss+2*y*rr*ss-rr**3) % p == 0
            else:
                assert (2*y*ss-rr*rr) % p == 0
            values = [pow(x,a,p)*pow(y,b,p)*pow(rr,c,p)*pow(ss,d,p)*pow(z,e,p) % p
                      for a,b,c,d,e in mons]
            for j, vector in enumerate(vectors):
                value = sum(a*b for a,b in zip(vector,values)) % p
                if value:
                    witness = {"quadratic_acceleration":quadratic,"basis_index":j,
                               "point":[x,y,rr,ss,z],"nonzero_value":value}
                    break
            if witness:
                break
        assert witness is not None
        witnesses.append(witness)
    # G=2X^2*S-X*R+Y illustrates positive contact at a zero direction.
    G = {(2,0,0,1,0):2,(1,0,1,0,0):-1,(0,1,0,0,0):1}
    local = linear_combination([(c,contact(a,0,0,0,5,p)) for a,c in G.items()],p)
    assert min(a[0]+3*a[1] for a in local) == 2
    normalized = linear_combination([(c,contact(a,0,0,1,5,p)) for a,c in G.items()],p)
    assert min(a[0]+3*a[1] for a in normalized) == 0
    return {"columns":C,"single_node_rank":L,"uniform_margin":C-n*L,
            "global_rank":rank,"kernel_dimension":len(vectors),"witnesses":witnesses,
            "old_universal_factor_claimed":False}


def main():
    controls = []
    for p in (17,257,2130706433):
        controls.append({"prime":p,"normalization_column_node_checks":normalization_checks(p),
                         "extension_controls":[extension_control(p,q) for q in (False,True)],
                         "full_kernel":full_kernel_control(p)})
    d = 2364-47
    production = []
    for T in (1042,1031,4156,2270):
        degrees = [r for r in range(1,9) if d > r*T]
        production.append({"source_T":T,"minimum_Z_degree":d,
                           "acceleration_degrees_with_guaranteed_properness":degrees})
    assert [x["acceleration_degrees_with_guaranteed_properness"] for x in production] == \
        [[1,2],[1,2],[],[1]]
    print(json.dumps({"status":"PASS_ACCELERATION_EXTENSION_CONTROLS",
                      "controls":controls,"conditional_production":production,
                      "general_proof_independently_reviewed":False,
                      "production_acceleration_degree_established":False,
                      "prize_bound_improved":False},sort_keys=True))


if __name__ == "__main__":
    main()
