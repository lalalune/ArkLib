#!/usr/bin/env python3
"""Three fixed-size tests of cross-deletion from balanced four-coset bases.

At each size choose the first valid pair, without optimizing for collisions.
No finite test is asserted to prove injectivity at the production domain size.
"""

import json
from hashlib import sha256

from astra_mca_paircover_four_cosets import label
from astra_mca_two_generator_probe import P, multiply, vanishing, evaluate, nullspace, projective


def linear_combination(a,b,sa,sb):
    return [(sa*(a[i] if i < len(a) else 0)+sb*(b[i] if i < len(b) else 0)) % P
            for i in range(max(len(a),len(b)))]


def divide_linear(f, root):
    q = [0]*(len(f)-1)
    carry = f[-1]
    for j in range(len(f)-2,-1,-1):
        q[j] = carry
        carry = (f[j]+root*carry) % P
    assert carry == 0
    assert multiply(q,[-root % P,1]) == f
    return q


def parity_weights(xs):
    weights = []
    for j,x in enumerate(xs):
        denominator = 1
        for i,y in enumerate(xs):
            if i != j:
                denominator = denominator*(x-y) % P
        weights.append(pow(denominator,-1,P))
    powers = [1]*len(xs)
    for _ in range(len(xs)-1):
        assert sum(weight*value for weight,value in zip(weights,powers)) % P == 0
        powers = [value*x % P for value,x in zip(powers,xs)]
    return weights


def cell(n):
    k,agreement = n//2,(2*n+1)//3
    omega = next(value for base in range(2,100)
        if (value := pow(base,(P-1)//n,P)) and pow(value,n//2,P) != 1)
    nodes = [pow(omega,i,P) for i in range(n)]
    assert len(set(nodes)) == n and pow(omega,n,P) == 1
    regions = [[e for e in range(n) if label(e,n) == j] for j in range(3)]
    polys = [vanishing([nodes[e] for e in region]) for region in regions]
    widths = [k-len(f)+2 for f in polys]
    columns = [(f,shift) for f,width in zip(polys,widths) for shift in range(width)]
    matrix = [[f[d-shift] if 0 <= d-shift < len(f) else 0
               for f,shift in columns] for d in range(k+1)]
    basis = nullspace(matrix)
    assert len(basis) == 2
    old = []
    wrows = []
    for vector in basis:
        u,v,w = vector[:widths[0]],vector[widths[0]:sum(widths[:2])],vector[sum(widths[:2]):]
        old.append([[0],multiply(polys[0],u),[-x % P for x in multiply(polys[1],v)]])
        wrows.append(w)
    chosen = None
    attempts = 0
    for xi in regions[0]:
        row_x = [evaluate(f,nodes[xi]) for f in wrows]
        for eta in regions[1]:
            attempts += 1
            row_y = [evaluate(f,nodes[eta]) for f in wrows]
            if (row_x[0]*row_y[1]-row_x[1]*row_y[0]) % P:
                chosen = xi,eta,row_x,row_y
                break
        if chosen:
            break
    assert chosen is not None
    xi,eta,row_x,row_y = chosen
    triples = []
    for root_index,row in ((eta,row_y),(xi,row_x)):
        combined = [linear_combination(a,b,row[1],-row[0]) for a,b in zip(*old)]
        assert all(evaluate(f,nodes[root_index]) == 0 for f in combined)
        triples.append([[0]]+[divide_linear(f,nodes[root_index]) for f in combined[1:]])
    f,g = triples
    assert all(len(poly) <= k for triple in triples for poly in triple)
    ab,ac,bc = [e for e in regions[0] if e != xi],[e for e in regions[1] if e != eta],regions[2]
    cores = [sorted(ab+ac+[xi,eta]),sorted(ab+bc),sorted(ac+bc)]
    assert all(len(core) == agreement-1 for core in cores)
    fv = [[evaluate(poly,x) for x in nodes] for poly in f]
    gv = [[evaluate(poly,x) for x in nodes] for poly in g]
    received = []
    for e in range(n):
        owner = next(j for j in range(3) if e in cores[j])
        value = fv[owner][e],gv[owner][e]
        assert all((fv[j][e],gv[j][e]) == value for j in range(3) if e in cores[j])
        received.append(value)
    classes, slots = {}, []
    for j in range(3):
        for e in range(n):
            if e not in cores[j]:
                residual = (received[e][0]-fv[j][e]) % P,(received[e][1]-gv[j][e]) % P
                assert residual != (0,0)
                direction = projective(*residual)
                classes.setdefault(direction,[]).append((j,e))
                slots.append((j,e,residual))
    assert sum(map(len,classes.values())) == n+2
    result = {"n":n,"k":k,"agreement":agreement,"primitive_root":omega,
        "first_valid_deleted_pair":[xi,eta],"pairs_tried_until_valid":attempts,
        "pair_region_sizes":list(map(len,(ab,ac,bc))),"private_A":[xi,eta],
        "mismatch_slots":n+2,"distinct_projective_directions":len(classes),
        "collision_classes":[slots for slots in classes.values() if len(slots)>1],
        "status":"ALL_DIRECTIONS_DISTINCT" if len(classes)==n+2 else "COLLISIONS_PRESENT"}
    if len(classes) == n+2:
        rotation = next(t for t in range(n+3)
            if all((b+t*a) % P for _,_,(a,b) in slots))
        scalars = []
        digest = sha256()
        for j,e,(a,b) in slots:
            scalar = -a*pow((b+rotation*a) % P,-1,P) % P
            scalars.append(scalar)
            support = cores[j]+[e]
            assert len(set(support)) == agreement
            witness = linear_combination(f[j],g[j],1+scalar*rotation,scalar)
            assert len(witness) <= k
            assert all(evaluate(witness,nodes[index]) ==
                (received[index][0]+scalar*(received[index][1]+rotation*received[index][0])) % P
                for index in support)
            short = cores[j][:k]+[e]
            weights = parity_weights([nodes[index] for index in short])
            syndrome = [sum(weight*(received[index][coordinate]
                + (rotation*received[index][0] if coordinate == 1 else 0))
                for weight,index in zip(weights,short)) % P for coordinate in (0,1)]
            assert syndrome != [0,0]
            assert (syndrome[0]+scalar*syndrome[1]) % P == 0
            assert syndrome == [weights[-1]*a % P,weights[-1]*(b+rotation*a) % P]
            digest.update(json.dumps([scalar,support,witness,short,weights,syndrome],
                                     separators=(",",":")).encode())
            digest.update(b"\n")
        assert len(set(scalars)) == n+2
        result.update({"basis_rotation_g_plus_t_f":rotation,"finite_bad_scalars":len(scalars),
            "parity_no_joint_certificates":len(scalars),"certificate_sha256":digest.hexdigest(),
            "status":"CERTIFIED_FINITE_MCA_WITNESSES_NOT_PRODUCTION_DOMAIN"})
    return result


def main():
    for n in (16,64,256):
        print(json.dumps(cell(n),sort_keys=True),flush=True)


if __name__ == "__main__":
    main()
