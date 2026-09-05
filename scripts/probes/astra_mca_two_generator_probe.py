#!/usr/bin/env python3
"""Exact two-generator MCA certificates on mu16 over the production prime.

This constructs 18 bad scalars on the 16-point code, not on the production
2^30-point code. In particular, it does not exceed the production field's
floor(P/2^128)=2^30 probability numerator budget.
"""

import json

P = 365375409332725729550921208179070755120141565953
N, K, AGREEMENT = 16, 8, 11


def multiply(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % P
    return c


def vanishing(roots):
    result = [1]
    for root in roots:
        result = multiply(result, [-root % P, 1])
    return result


def evaluate(a, x):
    result = 0
    for coefficient in reversed(a):
        result = (result*x+coefficient) % P
    return result


def nullspace(matrix):
    a = [row[:] for row in matrix]
    pivots = []
    for column in range(len(a[0])):
        row = len(pivots)
        pivot = next((j for j in range(row,len(a)) if a[j][column]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inverse = pow(a[row][column], -1, P)
        a[row] = [x*inverse % P for x in a[row]]
        for j in range(len(a)):
            if j != row and a[j][column]:
                multiple = a[j][column]
                a[j] = [(x-multiple*y) % P for x,y in zip(a[j],a[row])]
        pivots.append(column)
        if len(pivots) == len(a):
            break
    basis = []
    for free in sorted(set(range(len(a[0])))-set(pivots)):
        vector = [0]*len(a[0])
        vector[free] = 1
        for row,pivot in enumerate(pivots):
            vector[pivot] = -a[row][free] % P
        assert all(sum(x*y for x,y in zip(row,vector)) % P == 0 for row in matrix)
        basis.append(vector)
    return basis


def projective(first, second):
    assert first or second
    return (1, second*pow(first,-1,P) % P) if first else (0,1)


def parity_row(nodes):
    """A degree<K dual certificate on K+1 distinct evaluation points."""
    assert len(nodes) == K+1 and len(set(nodes)) == K+1
    weights = []
    for i,x in enumerate(nodes):
        denominator = 1
        for j,y in enumerate(nodes):
            if i != j:
                denominator = denominator*(x-y) % P
        weights.append(pow(denominator,-1,P))
    for degree in range(K):
        assert sum(weight*pow(x,degree,P) for weight,x in zip(weights,nodes)) % P == 0
    return weights


def experiment(ab, ac, private):
    omega = next(value for base in range(2,100)
        if (value := pow(base,(P-1)//N,P)) and pow(value,N//2,P) != 1)
    nodes = [pow(omega,i,P) for i in range(N)]
    assert len(set(nodes)) == N and pow(omega,N,P) == 1
    bc = sorted(set(range(N))-set(ab)-set(ac)-set(private))
    assert len(set(ab+ac+private)) == 10
    assert list(map(len,(ab,ac,bc,private))) == [4,4,6,2]
    polys = [vanishing([nodes[i] for i in region]) for region in (ab,ac,bc)]
    columns = [(f,shift) for f in polys for shift in range(K-len(f)+1)]
    matrix = [[f[k-shift] if 0 <= k-shift < len(f) else 0
               for f,shift in columns] for k in range(K)]
    basis = nullspace(matrix)
    if len(basis) != 2:
        return {"partition":[ab,ac,bc,private],"basis_dimension":len(basis)}
    low_columns = [(f,shift) for f in polys for shift in range(K-len(f))]
    low_matrix = [[f[k-shift] if 0 <= k-shift < len(f) else 0
                   for f,shift in low_columns] for k in range(K-1)]
    assert nullspace(low_matrix) == []
    triples = []
    for vector in basis:
        u,v = vector[:4],vector[4:8]
        triples.append([[0],multiply(polys[0],u),
                        [(-x) % P for x in multiply(polys[1],v)]])
    f,g = triples
    values_f = [[evaluate(poly,x) for x in nodes] for poly in f]
    values_g = [[evaluate(poly,x) for x in nodes] for poly in g]
    cores = [sorted(ab+ac+private), sorted(ab+bc), sorted(ac+bc)]
    assert all(len(core) == AGREEMENT-1 for core in cores)
    received = []
    for i in range(N):
        owner = next(j for j in range(3) if i in cores[j])
        value = (values_f[owner][i], values_g[owner][i])
        for j in range(3):
            if i in cores[j]:
                assert (values_f[j][i],values_g[j][i]) == value
        received.append(value)
    slots = []
    for j in range(3):
        for i in range(N):
            if i not in cores[j]:
                residual = ((received[i][0]-values_f[j][i]) % P,
                            (received[i][1]-values_g[j][i]) % P)
                if residual == (0,0):
                    return {"partition":[ab,ac,bc,private],"zero_residual_slot":[j,i]}
                slots.append({"core":j,"index":i,"residual":residual,
                              "projective":projective(*residual)})
    assert len(slots) == 18
    distinct = len({slot["projective"] for slot in slots})
    result = {"partition":[ab,ac,bc,private],"basis_dimension":2,
              "degree6_syzygy_dimension":0,"n":N,"k":K,"agreement":AGREEMENT,"prime":P,
              "projective_directions":distinct,"primitive_root":omega,
              "syzygy_basis":basis,"local_f":f,"local_g":g,
              "slots":slots,"received":received,"cores":cores}
    if distinct == 18:
        rotation = next(t for t in range(19)
            if all((b+t*a) % P for a,b in (slot["residual"] for slot in slots)))
        scalars, certificates = [], []
        for slot in slots:
            a,b = slot["residual"]
            scalar = -a*pow((b+rotation*a) % P,-1,P) % P
            scalars.append(scalar)
            j,i = slot["core"],slot["index"]
            support = cores[j]+[i]
            assert len(set(support)) == AGREEMENT
            for x in support:
                lhs = (received[x][0]+scalar*(received[x][1]+rotation*received[x][0])) % P
                rhs = (values_f[j][x]+scalar*(values_g[j][x]+rotation*values_f[j][x])) % P
                assert lhs == rhs
            short = cores[j][:K]+[i]
            weights = parity_row([nodes[index] for index in short])
            syndrome = [sum(weight*(received[index][coordinate]
                + (rotation*received[index][0] if coordinate == 1 else 0))
                for weight,index in zip(weights,short)) % P for coordinate in (0,1)]
            # A joint degree<K explanation would make BOTH syndromes zero.
            # At least one is nonzero, while their scalar combination vanishes.
            assert syndrome != [0,0]
            assert (syndrome[0]+scalar*syndrome[1]) % P == 0
            assert syndrome == [weights[-1]*a % P,weights[-1]*(b+rotation*a) % P]
            witness = [(x+scalar*(y+rotation*x)) % P
                       for x,y in zip(f[j]+[0]*(K-len(f[j])),g[j]+[0]*(K-len(g[j])))]
            assert len(witness) == K
            assert all(evaluate(witness,nodes[index]) ==
                (received[index][0]+scalar*(received[index][1]+rotation*received[index][0])) % P
                for index in support)
            certificates.append({"scalar":scalar,"core":j,"extra_index":i,
                "support_indices":support,"witness_coefficients":witness,
                "parity_indices":short,"parity_weights":weights,"received_syndrome":syndrome})
        assert len(set(scalars)) == 18
        result["basis_rotation_g_plus_t_f"] = rotation
        result["bad_scalars"] = scalars
        result["mca_certificates"] = certificates
        result["parity_certificate_count"] = len(certificates)
        result["production_probability_numerator_budget"] = P//2**128
        result["status"] = "18_CERTIFIED_FINITE_MU16_MCA_WITNESSES_NOT_PRODUCTION_DOMAIN"
    return result


def main():
    result = experiment([0,1,4,9],[2,6,11,15],[5,13])
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
